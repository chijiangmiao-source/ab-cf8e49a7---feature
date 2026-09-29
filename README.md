# 姿态执行器保护脚本审计服务(octagon-auditor)

对姿态执行器保护脚本做**八边形抽象域**上的静态验证:上传前必须证明每次点火、
转向或增压指令(以包线断言建模)在所有可达程序点上都被不变量蕴含,绝不因有限
回放恰好未触发危险分支而放行。包线审计通过后,工程师还可对**同一份脚本**发起
终止性复核(`POST /recheck`),证明任一可达控制路径最终到达 halt/顺序终止,
而非只看到存在一个可达终止点。服务零第三方依赖,仅使用 Python 标准库。

## 输入模型

`POST /audit` 接收 JSON:

```json
{
  "num_registers": 2,                      // 1..4 个整数寄存器
  "initial": [{"lo": 0, "hi": 0},          // 每寄存器初始范围;lo/hi 可为 null(无界)
               {"lo": -5, "hi": 5}],
  "instructions": [ ... ]                  // 1..48 条,id 必须恰好为 0..N-1(稳定编号)
}
```

指令集(且仅含):

| op      | 字段                 | 语义                                   |
|---------|----------------------|----------------------------------------|
| `set`   | `reg`, `value`       | 常量赋值 `x_reg := value`              |
| `add`   | `reg`, `value`       | 常量增减 `x_reg := x_reg + value`      |
| `sub`   | `reg`, `value`       | 等价于 `add` 取负                      |
| `branch`| `cond`, `target`     | 比较分支,假方向顺序下落                |
| `goto`  | `target`             | 无条件跳转                             |
| `assert`| `cond`               | 包线断言(点火/转向/增压的允许包线)   |
| `halt`  | —                    | 终止;顺序走出末尾亦视为到达终止       |

条件为八边形片段:`{"coefs": {"0": 1, "1": -1}, "op": "<=", "value": 5}` 表示
`x0 - x1 <= 5`;`coefs` 至多两项、系数 ±1,比较符 ∈ `<= < >= > == !=`。
解析时统一规范化为 `<= / == / !=` 形态,响应中的条件文本均为规范化形式。

## 分析方法

- **八边形约束**:以差分界矩阵(DBM)维护各程序点 `±x_i ± x_j <= c` 形式的
  不变量,Floyd–Warshall 最短路 + 八边形整值 tightening 得到强闭包;
  `set`/`add`/分支收窄均为精确迁移(整数寄存器,减半步骤向下取整)。
- **回边闭包与 widening**:DFS 回边目标处施加固定规则 widening
  (凡变弱的分量放宽为 +∞),保证上升迭代终止。
- **widening 后持续复算**:自后不动点出发做下降迭代(Gauss–Seidel 取交),
  逐步回收 widening 损失的精度,每一步仍是后不动点。
- **终态校验**:输出前逐条转移显式复核 `f(inv[p]) ⊑ inv[q]`;响应中逐程序点
  给出规范化闭包约束与入边来源(`points.<id>.invariant` / `.incoming`),
  调用方可独立重放同一检查。

## 结论形态

- **`pass`**:每个可达断言均被该点不变量蕴含。附逐点不变量、入边来源、
  每条断言的逐项界核对(`assertions[].bounds`)与不动点元信息。
- **`fail`**:存在不可证断言。`first_unproven` 给出**首个按程序点编号**稳定
  裁决的位置、进入该点的抽象边界(`abstract_state`)及未被涵盖的包线条件
  (`uncovered`,含不变量实际能给出的界)。`kind: "abstract_alarm"` 明示这是
  抽象上近似告警,**并非具体执行反例**。不可达点上的断言记 `unreachable`,
  不阻塞放行。
- **`error`**:结构问题——寄存器越界、跳转悬空、不可解析约束、无可达终止等
  **合并反馈**于 `errors` 列表;响应不携带任何分析证据(无状态服务,每次请求
  独立计算,不存在旧证据)。

已知精度边界:`!=` 的真方向与 `==` 的假方向不是八边形约束,按恒等(不收窄)
处理,保持可靠但可能产生抽象告警。

## 终止性复核(`POST /recheck`)

包线审计结论为 `pass` 的同一份脚本可提交到 `/recheck`(请求体与 `/audit`
完全相同;服务无状态,内部复用同一套结构校验、不动点不变量与终态校验):

- **可行性剪枝**:仅对源点可达、且经八边形迁移(含分支 guard 收窄)后非空的
  *活跃转移*推导关系,不可行方向不计入循环;
- **强连通区(SCC)**:在活跃转移图上用 Tarjan 求 SCC,非平凡 SCC 即循环;
- **逐寄存器单调关系**:为每条活跃转移推导 `x'_r op x_r`,
  `op ∈ {<, <=, ==, >=, >, ?}`(未知)。`add c` 按 c 符号直接判定;
  `set c` 以源点不变量给出的 x_r 区间判定;guard/恒等边为 `==`;
  缺信息给 `?`,**绝不臆造下降**;
- **SCC 内闭包**:按关系复合半格对所有路径做 Kleene 闭包(A*),并单独提取
  长度 ≥1 的闭环关系(避免空路径 `==` 掩盖严格性)。分支交替时,一条路径的
  局部严格下降会与另一条非严格路径 join 成 `<=`/`?`,**不会被误作全局进展**;
- **排名判定**:对每个循环寻找一个寄存器,其在每个循环程序点的闭环关系都
  严格(下降 `<` 配不变量有限**下界**,或上升 `>` 配有限**上界**;后者即
  `-x` 严格下降)。严格整数变化配有限界 ⇒ 循环不可能无限重复。

### 结论形态(终止性)

- **`terminating`**:`loops.{total,proven,unproven}` 统计循环;每个已证循环
  附**可独立重放的循环证书** `certificates[]`:
  - `loop_head` / `points` / `exit_edges`:稳定标识的循环程序点与退出转移;
  - `internal_edges[].register_relations`:逐活跃转移的寄存器关系(可独立复核);
  - `closed_cycle_relations`:每点长度 ≥1 的闭环关系;
  - `ranking_register` / `ranking_direction`(`decreasing`/`increasing`)
    / `ranking_lower_bounds` 或 `ranking_upper_bounds`:排名寄存器与每点界,
    界可对照 `/audit` 响应里的同名逐点不变量独立核对。
- **`cannot_prove`**:`first_unproven_loop` 以**稳定程序点**(SCC 内最小编号
  循环头)给出该循环的逐转移关系、闭环关系与每寄存器候选,`first_missing`
  说明首个无法证明的循环关系究竟缺*严格变化*(`strict_decrease`)还是缺
  *有限界*(`lower_bound`/`upper_bound`)。`kind: termination_proof_failure`
  明示这是**证明失败(抽象信息不足),并非断言存在实际死循环**,不得据此伪造
  无限执行;其余已证循环仍在 `certificates` 中给出。
- **`error`**:`structural_errors` 与 `/audit` 完全一致(合并反馈、不携带任何
  旧结论/证书);`envelope_audit_not_passed` 表示脚本尚未取得 `pass` 的包线
  结论(附 `first_unproven_point`),复核被拒绝。

已知能力边界:排名只认单个寄存器的严格单调(含 `-x` 对称方向);需要词典序
(如内外层不同计数器)或别名和(Sum 类)排名的循环会保守地返回 `cannot_prove`,
不会误判。

## 运行

```bash
# 本地
PORT=8080 python -m app.server
curl localhost:8080/health
curl -X POST localhost:8080/audit -d @script.json
# 包线审计通过后,同一份脚本可发起终止性复核
curl -X POST localhost:8080/recheck -d @script.json

# Compose(宿主机端口可配置,默认 8080)
AUDIT_HOST_PORT=9090 docker compose up --build app
```

接口:`GET /health`(健康路径)、`GET /`(服务信息)、
`POST /audit`(包线审计)、`POST /recheck`(包线通过后的终止性复核)。
容器内端口由 `PORT` 配置,宿主机映射由 `AUDIT_HOST_PORT` 配置。

## 验证(verify 容器)

```bash
docker compose up --build --exit-code-from verify --abort-on-container-exit verify
```

`verify` 容器依次执行并以退出状态码报告结果(0 通过 / 1 失败):

1. **代码测试**:`python -m unittest discover -s tests -t .`(53 个用例,
   覆盖八边形域、分析器、终止性复核关系代数/循环判定与 HTTP 接口);
2. **镜像构建检查**:`verify` 阶段 `FROM app` 阶段构建,构建 verify 即复核
   app 镜像可构建;冒烟时再将 `/health` 返回的版本与 `EXPECTED_VERSION` 比对,
   确认运行中的镜像即期望构建;
3. **HTTP 冒烟**(`scripts/smoke.py`):等待健康路径就绪后,核对放行用例
   (含循环关系不变量)、未证告警用例(首个未证点、抽象边界、未涵盖条件)、
   结构错误合并反馈用例(四类错误齐备且无旧证据);终止性复核覆盖单调计数
   循环、分支交替仍终止、一升一降伪进展、无界自增闭环与审计门禁,并复测
   无状态性与 `/audit` 回归。

## 目录结构

```
app/octagon.py     八边形域:DBM、强闭包、迁移函数、格运算、规范化约束输出
app/program.py     指令解析、结构校验(合并反馈)、控制流图、widening 点
app/analyzer.py    上升/下降不动点引擎、终态校验、断言蕴含判定、两接口共享流水线
app/termination.py 终止性复核:活跃转移、SCC、单调关系闭包、排名判定、循环证书
app/server.py      HTTP 服务:GET /health,POST /audit,POST /recheck
tests/             单元测试(unittest,零依赖)
scripts/smoke.py   verify 容器的 HTTP 冒烟
Dockerfile         多阶段:app(运行)/ verify(验证)
docker-compose.yml app 服务(可配置宿主机端口)+ verify 容器
```

# client-synthesizer0

> **For vostd maintainers:** the specification defects found at vostd `8e4b202d6`, each with the code, a
> failing client, Verus's error and how to fix it, are in
> [findings/defects-8e4b202d6.md](findings/defects-8e4b202d6.md) (English).
> At vostd `eb1a9d044`, compared with that list (9 fixed upstream, 6 new): [findings/defects-eb1a9d044.md](findings/defects-eb1a9d044.md).

为[vostd](https://github.com/asterinas/vostd) (Asterinas内核`ostd`的Verus验证版本) 合成**按真实用法调用API的client**, 用它们检验规格是否够调用者用; 列出并审计Verus信任而不检查的代码.

这是[vostd-client-synthesizer](https://github.com/alpha-beta-eta/vostd-client-synthesizer) (下称"前身") 的整理版, 一个单独的仓库. 前身是一系列探索 (2026-11-06到2026-11-15, 记录在前身的`docs/`) 的累积: 每次试验都留下了代码, 选项和数据格式, 有的后来被更好的做法取代, 有的只为一次实验存在. 本版只保留确实带来结论的部分, 把试验中遇到的细节问题按原则一次改好, 而不是继续修补. 结果不要求与前身逐个client一致.

设计和取舍见[docs/design.md](docs/design.md); 各阶段方法的概览 (重点是client的枚举) 见[docs/methods.md](docs/methods.md), 一路踩过的坑见[docs/pitfalls.md](docs/pitfalls.md). 一轮评估的固定次序 (每步的命令, 谁做, 核对什么) 见[docs/workflow.md](docs/workflow.md), 给LLM照做的skill在`.claude/skills/client-synthesizer0/`. 前身的文档 (`docs/`, 本机上是`../vostd-client-synthesizer/docs/`) 记录了每个决定的来历和测量, 本版的文档只引用, 不重复.

## 与前身相比

### 保留的 (都已证明有收益)

| 部分 | 收益的依据 |
|---|---|
| 由VIR和源码按跨度对齐抽取API表, 探针核对 (含空洞的requires = 不可调用的方法) | mm, sync的requires 91%取源码的写法; 探针的`vacuous`机械地找出DMA的18个不可调用的继承方法 (enumeration.md 14) |
| 良构性检查, 渲染, 运行 (每个client一个z3, 编译错误和崩溃的处理, 续跑的键) | 一轮从7小时到26分钟 (time-sinks A1); 键防止沿用过时的结果 (C15) |
| **goal族** (前身的goal-plan): 对每个API G的每条requires, 只放G的实参所依赖的调用; 产生, 修改, 出错之后, 再调用, 往返, 由ensures向前 (R4) | 以一条规则代替chain, flow, repeat和手列的形状 (enumeration.md 7, 9, 15); 找到`from_unique`的ref_count缺口 |
| claim, protocol族 (调用知识的假设) | 已确认缺陷的主要来源之一 |
| `assume(!P)`处理`P ==> may_panic()` | r28中162个client由失败变为通过, 失败之后的事实才量得到 (enumeration.md 17) |
| 分组 (按子句的身份), 连锁失败的先后, 已知问题按事实挂上 | 组数由1475降到807 (按文本→按身份); triage.md 2 |
| 证否, 归因, 责任者证得出吗 (provable), 确认 (confirm), 包装函数丢了什么 (drops) | 分诊的机械化 (triage.md); 一轮确认N13–N23 |
| 已知问题的回归, 判定的存储和核对 | 换版本时第一个问题 (design.md 3.11) |
| 可信代码的列举, 审计判定的核对, 演示 | 与client正交的另一类缺陷 |

### 改了的 (原来是修补, 现在按原则)

| 问题 | 前身 | 本版 |
|---|---|---|
| client放在被测模块**之内** (子模块), 看得见closed的体和私有字段, 比真实调用者强, 系统地漏掉"结果只由closed函数描述"一类缺陷 (enumeration.md 17.3, 20) | `work/t3-sibling.rkt`在4个模块上单独试 | client一律放在被测模块的**兄弟**模块 (`<parent>::cs_clients`); 导入照抄模块顶层的`use`. 只有找不到父模块文件时才退回子模块, 并在target中记`(placement child)` (design.md 3.8) |
| 哪些ensures子句没有client检验 | X9: 每条子句一次Verus运行 (一个模块几十轮), 换种子, E2 | `coverage`: 一次带`--log smt`的运行, 离线给每个合取项加守卫, 用z3求unsat core和逐条的必需性 (enumeration.md 18, 与X9给出同样的子句); rlimit和`unknown`记为未知 (19) (design.md 3.10) |
| 必须关闭的类型 (锁的guard) | 每个模块一个手写的覆盖表 (`auto/manual/`), 里面只有这一行 | 调用知识的一种条目`(must-close TYPE (why ..))`, 由`knowledge`检查核对; 不再有手写的覆盖表 (原则10) |
| 已知问题的证人期望 | 可以是渲染出的文本的正则, 渲染一改就失配 (time-sinks C16) | 只按子句的身份: `(requires API N)`, `(claim)`. 文本的期望读入但不用, 报为`no-witness`并说明要改写; `witness`命令直接给出身份 |
| 额外的Verus参数 | 环境变量`CS_VERUS_ARGS` (只供试验, 不进续跑的键) | `run.rkt`的参数`verus-extra-args`, 只由`coverage`设置 |
| 过时的item-index | 不支持`--full-spans`时悄悄地全部退回VIR的写法 (2026-11-16发现: 环境中的旧构建使源码对齐为0) | 抽取时拒绝, 要求重建 |
| 配置 | `chain`的深度, 上限, 每模块的覆盖, 不认识的键被忽略 | 只有`auto`, `providers`, `knowledge`, `identity`, `modules`, `families`, `elided-lifetimes`; 不认识的键是错误 |

### 去掉的

| 部分 | 为什么 |
|---|---|
| chain, flow, repeat族, goal的手列形状 | goal族以一条规则问同样的问题, 每个client回答一个问题; chain在深度上指数增长, 要预算和降级 (enumeration.md 7, 9) |
| post (Houdini式的后条件合成) | 候选少, 判定难; "函数证得出而不导出"由drops和provable更直接地回答 |
| retry (按名字插入引理再跑) | 证否和provable回答了它要回答的问题 (缺的是规格还是调用者的证明) |
| 单表命令`gen`, `chains`, `enum` | 只为调试已删去的族 |
| `auto/manual/`覆盖表 | 见上 (must-close) |
| X9的变异轮次, 换种子, E2 | coverage代替; X9只在对coverage的个别结果有疑问时手工复核 (前身的`work/x9-mutate.rkt`) |
| 前身`work/`中的一次性脚本 | 结论已写进前身的文档 |

没有做的 (前身time-sinks中未解决的): 长协议展开的缓存 (A13), 模块之间并行生成 (A10). 它们只影响时间, 不影响结论.

### 从零重做的检查 (2026-11-16, vostd 8e4b202d6)

删去全部表, 从VIR重新扫描 (35个模块, 抽取, 修补, 探针, 15分钟), 再在5个模块上评估 (`data/configs/check.rktd`, 77秒), 与前身的r28 (子模块) 逐个client比较:

- **生成的client与r28逐个相同** (没有只在一边的client): 原则10所要求的"重做得到同样的东西", 在这5个模块上成立.
- 探针: 30个模块与前身的表的`ok`数相同. 不同的: dma_coherent 22→28, dma_stream 37→49 (前身数据早于继承的默认方法进表); spin 18→15, rcu 22→20 (私有类型`SpinLockResource`, `RcuInner`的方法, 别的模块写不出它们); rwmutex 35→29 (6个`fmt`/`fmt_req`: 源码写`fmt::Debug`, 兄弟中`Debug`有几个候选, 机械的修补不取; 前几轮已判为不是缺陷).
- 状态的变化恰是兄弟模块的实验 (前身enumeration.md 20) 预言的: segment 25个由通过变为失败 (`split`, `From<Frame>`的结果不透明, 已确认的缺陷), spin 3条`wf`的claim由通过变为失败 (候选); unique, mutex, wait逐个不变.
- `coverage`在segment上: 20条ensures中9条被检验 (运行2分钟), 与前身T1在r28上的条数相同; 差别是`split` #1不再被检验 (依赖它的client在兄弟中失败了), `size` #1被检验.

这次检查还发现: 环境中item-index的旧构建使前身的抽取悄悄退回VIR的写法 (见上表).

## 开始

需要: Racket 9.x, git, rustup, vostd的一个专用检出 (`dv`子模块, `tools/verus`), 用检出的verus_syn编译的`tools/item-index`. 准备环境的步骤与前身相同 (前身的`.claude/skills/client-synthesizer/SKILL.md`第0节). 本机的路径写在本目录的`env.local.rktd`.

```bash
raco make cli.rkt && raco test tests
```
```bash
racket cli.rkt env
```

数据按惯例放在本目录的`data/`, 运行结果在`out/` (都不进git). 一轮评估:

1. 建表 (每次vostd更新后): 导出VIR, 然后
   ```bash
   racket cli.rkt scan VIR '^ostd::(mm|sync|cpu|util|boot|task)(::|$)' data/auto out/scan
   ```
2. 核对调用知识 (`data/auto/knowledge/`, 格式见前身的`docs/knowledge-format.md`, 加上本版的`must-close`):
   ```bash
   racket cli.rkt knowledge data/auto data/auto/knowledge
   ```
3. 生成并运行client, 分组:
   ```bash
   racket cli.rkt evaluate data/configs/all.rktd out/r1
   ```
   ```bash
   racket cli.rkt groups out/r1 data/auto/knowledge data/issues --verdicts data/verdicts
   ```
4. 覆盖 (哪些ensures没有client检验):
   ```bash
   racket cli.rkt coverage out/r1
   ```
5. 分诊和确认: `refute`, `provable`, `confirm`, `drops` (前身的`docs/triage.md`); 已知问题: `regress`, `regress-report`.

命令的完整列表在`cli.rkt`的开头.

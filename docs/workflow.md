# 工作流: 一轮完整的评估

本文是client-synthesizer0一轮评估的**固定次序**: 每一步的命令, 由谁做, 跑完核对什么, 什么情况下停下. 给LLM (Claude Code, 按[skill](../.claude/skills/client-synthesizer0/SKILL.md)) 和人逐步照做; 次序和命令只在本文中改, 不在执行时临时改. 每一步的原理见[design.md](design.md), 判定的细节见前身的`docs/evaluation.md`和`docs/triage.md` (本机上是`../vostd-client-synthesizer/docs/`); 本文只引用, 不重复.

前身的`docs/workflow.md`还写着本版已去掉的部分 (chain, flow, repeat族, `retry`, `post`, `data/auto/manual/`, 手写的表`data/apis/`, `enum`); 本版不做那些步骤.

每一步标明谁做:

- **[工具]** 机械的, 本仓库的程序, 结果可重复. 照做, 不改参数.
- **[LLM]** 判断或写数据; 写下的东西还要经过后面的机械检查.
- **[人]** 要人决定的. LLM不代做, 停下来问.

工具只产出事实. 是不是规格缺陷是判断, 只有经过第F步的机械确认才写成"已确认".

## 0. 约定

一轮的名字和位置先定下, 下文都用这些名字:

| 名字 | 含义 | 例 |
|---|---|---|
| `RUN` | 这一轮的运行目录 | `out/r1` |
| `REG` | 这一轮已知问题的回归目录 | `out/g1` |
| `CFG` | 评估的配置 | `data/configs/all.rktd` |
| `VIR` | 这个提交的VIR (`.fasl`缓存) | `env.local.rktd`所在机器上的`vir-<提交>/crate.fasl` |
| `COPY` | 同一提交的**另一份**干净的vostd检出, 供`provable`/`confirm`改写 | `/root/cs-work/vostd-cs0` |

- 命令都在仓库根目录跑, `racket cli.rkt ..`; 每条命令的输出重定向到`out/<RUN的名字>-<步骤>.log`. 长的放后台, 不要轮询.
- 本机的环境在WSL中 (`env.local.rktd`的路径是WSL的). 从Git Bash调用时加`MSYS_NO_PATHCONV=1`, 否则`/mnt/d/..`被改写成Windows路径: `MSYS_NO_PATHCONV=1 wsl -e bash -lc 'cd /mnt/d/client-synthesizer0 && ...'`.
- 会改写检出的步骤 (D, E2, E3, F) **一次只跑一个**: 它们都往vostd检出 (或`COPY`) 中写client模块.
- 结果数据 (`data/`, `out/`, `work/`) 不进git. 只有对合成器本身的修改 (`lib/`, `cli.rkt`, `tests/`, `docs/`) 提交.

## A. 环境 [工具]

1. `racket cli.rkt env`. 必须: `vostd ok`, `(tables-at ..)`与HEAD `same`, `(changes 0)`, `dv ok`, `tools/verus ok`, `item-index ok`, `target-dir ok`. 不满足就停下.
   - `changes`不是0, 且改动只是`mod cs_clients;`, `cs_clients.rs`和`Cargo.lock` (上一次运行被中断): 先看`git -C <vostd> diff`确认只有这些, 再`git checkout -- Cargo.lock <模块文件>`, 删去`cs_clients.rs`. 有别的改动就停下, 问人.
2. 换了检出或Verus之后 (同一提交上重跑时不必): 原版`ostd`必须0 errors (`cargo dv verify --package ostd`, 在检出中). 不是0就停下.
3. `raco make cli.rkt && raco test tests`. 必须全部通过.

在新机器上准备环境的步骤见前身的`.claude/skills/client-synthesizer/SKILL.md`第0节 (README"开始").

## B. 表和调用知识

只在vostd换了提交之后做 (前身evaluation.md 3.1, 逐层, 一次一层). 同一提交上的新一轮跳过B1, B2.

1. **[工具]** 导出VIR (检出要干净): `cargo dv focus --package ostd -- --no-verify --log vir --log-dir <目录>`; `racket cli.rkt vir-cache <crate.vir> VIR`.
2. **[工具]** `racket cli.rkt scan VIR '^ostd::(mm|sync)(::|$)' data/auto out/scan`. 核对: 每个模块的探针`ok`数, 与上一次的表逐个比较; 由`ok`变坏的分清是vostd还是工具. 一类条目一起坏是抽取的bug, 改合成器 (H), 不逐条手修.
3. **[工具]** `racket cli.rkt knowledge data/auto data/auto/knowledge > out/<RUN>-knowledge.log`. 每个模块必须`ok`, `(anchors .. (lost 0) (ambiguous 0))`. `(protocol-left-out NAME (API REASON) ..)`不是问题: 协议调用了抽取时按记下的原因 (`left-out.rktd`: `closure-bound`等) 留在表外的API, 这个协议不生成; 记下条数和原因, 不停下. `(protocol-outside ..)` (调用的API不在表中, 也没有记下的原因) 才是问题. `moved`的: `--fix`; 被标出漂移的条目 **[LLM]** 对照新源码重读, 读过之后才`--accept`. 不重读就不`--accept`.

## C. 生成和运行 [工具]

1. `racket cli.rkt evaluate CFG RUN > out/<RUN>.log`. 可续跑 (键: client, 表的导入, 展开后的client, render.rkt和run.rkt, 检出的状态).
2. 核对`RUN/modules.rktd`, 每个模块:
   - `(sanity ok)`才可信. `not-verified`的模块没有被验证: 读`RUN/results/<m>/verus-*.out`和`results.rktd`的`(unattributed ..)`, 查明原因 (编译错误不在client中时整个模块不被验证). 是工具的问题就改合成器 (H) 再只重跑这个模块; 不能把它当作"全部失败"汇报.
   - `(clients 0)`的模块: 没有可调用的条目, 记下.
   - `(dropped-imports ..)`, `(imports ..)`: 导入轮次的事实 (design.md 3.8), 记下.
3. 注意: 续跑的键不含`evaluate.rkt`. 改了`evaluate.rkt`的导入轮次之后, 要重跑的模块手工删去`RUN/results/<m>/key.sha`.

## D. 分组 [工具]

`racket cli.rkt groups RUN data/auto/knowledge data/issues --verdicts data/verdicts > out/<RUN>-groups.log`.

核对: 组数; 每组的`(labels ..)`; 没有标签 (或只有`stale-verdict`) 的组是这一轮的**新组**, 列出来 (模块, 键, `(at ..)`). `stale-verdict`的组要重判. `(timeouts N)`不是0的模块记下.

## E. 机械的分诊 [工具]

依次跑, 每步之后都再跑一次D (标签会变):

1. **覆盖**: `racket cli.rkt coverage RUN > out/<RUN>-coverage.log`. 记下每个模块的`clauses`/`checked`/`unknown`/`unchecked`. 可续跑.
2. **证否**: `racket cli.rkt refute RUN > out/<RUN>-refute.log`. 记下`refuted`/`open`/`no-assertion`的数. 被证否的组, 原来有标签的: 核对与标签是否一致 (`noise`, `by-design`应当被证否; `defect`被证否是矛盾, 停下来查).
3. **责任者证得出吗**: 先`--dry`看哪些组被试, 再跑:
   ```bash
   racket cli.rkt provable RUN COPY --dry --unlabelled data/auto/knowledge data/issues data/verdicts
   ```
   ```bash
   racket cli.rkt provable RUN COPY --unlabelled data/auto/knowledge data/issues data/verdicts > out/<RUN>-provable.log
   ```
   `--unlabelled`只试新组 (D中没有标签的); 不加时试所有不是噪音, 没被证否的组 (要更久, 换提交之后做一次). `COPY`要与运行同一提交, 干净, 不是环境的检出 (第0节). 第一次运行把所选的组记在`RUN/provable/selection.rktd`, 续跑 (包括F写下判定之后重走本步) 试的是同样的组, 结果照旧. 它拒绝续跑的只有: 换了模式 (加上或去掉`--unlabelled`), 记下的组在运行中没有了, 候选子句变了 (运行或表变了). 那时要试新的组, 删去`RUN/provable/`和`RUN/confirm/`重跑.
4. **确认**: `racket cli.rkt confirm RUN COPY VIR > out/<RUN>-confirm.log`. 读`RUN/confirm/facts.rktd`: 每条子句`alone`或`together-only`, `rests-on`; 每组`fixed`/`reduced`/`unchanged`, `confirmed`与否; 每个模块的`sanity`和`(new ..)`. 跑完`COPY`必须仍然干净 (`git -C COPY status --short`为空).
5. **回归**: `racket cli.rkt regress CFG data/issues REG > out/<REG>.log`, 然后`racket cli.rkt regress-report data/issues REG > out/<REG>-report.log`. `present`的照旧; `gone`/`undetected`的对照diff判定; `no-witness`的记下 (文本的期望要改写成`(requires API N)`或`(claim)`: `racket cli.rkt witness RUN CLIENT ..`).

## F. 判定 [LLM, 人决定]

对D中的每个新组 (先`(proves ..)`的组), 按前身evaluation.md 7.3判定, 写一句理由:

- 读被调用者的规格, 必要时读函数体和上游的实现; 先查已知问题和已有的判定中是否已处理过同一函数.
- 问: 真实调用者需不需要这个事实? 同级的函数给了吗? 下层的给了吗?
- 机械的事实先看: `refute`的`refuted` (client所问的在那里不成立), `provable`的`proved` (责任者有而不给), `confirm`的`confirmed`, `rests-on`.
- 判定用`racket cli.rkt verdict RUN MODULE KEY JUDGEMENT REASON data/verdicts/round-<日期>.rktd [--issue ID]`记下. JUDGEMENT: `defect`, `not-defect`, `noise`, `by-design`, `known`, `needs-lemma`, `decision`. `decision` (要维护者决定) 和`defect`的汇报给人, 由人决定.
- 写成"已确认的缺陷"的条件: `confirm`中`confirmed`, 或按前身evaluation.md第8节手工走完 (失败的client通过且没有新的空洞, 被改的模块0 errors, 整个ostd 0 errors, 合并补丁后再验证一次). 修改只加ensures, 循环不变式, 几行证明; 不加`assume`/`admit`/`external_body`.
- 确认了的写进`data/issues/` (格式`lib/model/issues.rkt`), 证人用`witness`取出, 期望按子句的身份.

判定完再跑一次D: 新组应当都有了标签.

## G. 可信代码 [工具, LLM审计, 人决定]

`racket cli.rkt trusted`; `racket cli.rkt audit data/audit/verdicts [演示的运行]`: 报告变了的, 没了的, 未判定的, 不一致的. 变了的对照diff重新判定后才`--accept`; 不一致的由人决定 (design.md 3.12).

## H. 记录 [LLM起草, 人决定]

一轮的记录写在用户指定的地方 (不在本仓库): vostd提交, Verus版本, 配置, 每一步的数字 (C的通过/失败, D的组数和新组, E各步的结果), 每个判定和理由, 待人决定的. 区分工具给出的事实和判断.

## I. 改合成器时 [LLM/人改, 工具回归]

执行中发现工具的bug时: 停在那一步, 改合成器, 再从那一步接着做. 每次:

1. 原理先写进design.md (或本文), 再改程序.
2. `raco make cli.rkt && raco test tests`; 新的规则加测试 (`tests/`).
3. 涉及生成, 渲染或运行的: 对同一批client改动前后各跑一次, `racket cli.rkt compare`逐个比较, 每个变化都要解释 (只看总数会漏掉).
4. 一次修改一个提交, 提交信息写清楚问题和规则. 不推送, 除非用户要求.

## 不要做的

- 跳步, 换次序, 或临时改命令的参数. 要改先改本文.
- 不看`sanity`就用`verified`; 把`not-verified`的模块当作结果.
- 为了让client通过而加requires, 加强表的requires, 删掉失败的断言.
- 把调用知识 (特别是`limitation`) 当作判定; 没重读就`knowledge --accept`.
- 只凭阅读把修改写成"已确认".
- 在用户的vostd工作区中改动; 两个改写检出的步骤同时跑.
- 拿上一次的中间结果当作已知正确; 只看汇总数字.

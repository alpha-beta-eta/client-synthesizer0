---
name: client-synthesizer0
description: 用client-synthesizer0 (本仓库) 对vostd (Verus验证的Asterinas内核ostd) 跑一轮评估: 生成并运行client, 分组, 覆盖, 证否, provable/confirm, 已知问题的回归, 判定, 审计可信代码. 用户要求"跑一轮评估", "跑全部模块", 分诊新的失败组, 确认缺陷, 或运行本仓库cli.rkt的evaluate/groups/coverage/refute/provable/confirm/regress/verdict/trusted/audit时使用.
---

# 用client-synthesizer0跑一轮评估

仓库 (下文`$CS`): 本skill的上三层, 其中有`cli.rkt`. 一轮评估的**固定次序**在`$CS/docs/workflow.md`: 每一步的命令, 谁做, 跑完核对什么, 何时停下. **严格照它做**:

1. 开始前读完`docs/workflow.md`和`README.md`. 原理在`docs/design.md`; 判定的细节在前身的`docs/evaluation.md`和`docs/triage.md` (`$CS/../vostd-client-synthesizer/docs/`).
2. 按A, B, C, ..的次序做, 不跳步, 不换次序, 命令的参数照抄. 第0节的名字 (`RUN`, `REG`, `CFG`, `VIR`, `COPY`) 先定下, 告诉用户.
3. 每一步跑完, 按该步写的"核对"逐项核对, 把数字记下来; 不满足就停下, 告诉用户是哪一步, 哪一项, 输出在哪里.
4. 记录的规则 (workflow.md F5, 2026-11-17用户定): 机械地确认了且没有标记的`defect`直接记下, 不问; 标为**[人]**的, `decision`, 带标记的`defect`, 判定之间的冲突, 不代做, 在F5汇总后**一次**问用户. 中途不为这些停下.
5. 发现工具的bug时按第I节: 先写原理, 再改程序, 加测试, 跑测试, 单独提交, 然后从出错的那一步接着做. 不绕过, 不手工修补结果文件.
6. 发现workflow.md本身不对或缺一步时, 不临时变通: 告诉用户, 改了workflow.md之后再做.

本机的环境在WSL中: 从Git Bash调用时`MSYS_NO_PATHCONV=1 wsl -e bash -lc 'cd /mnt/d/client-synthesizer0 && ...'`. 长的命令放后台, 输出重定向到`out/`下的日志, 不要轮询.

结果数据 (`data/`, `out/`, `work/`) 不进git; 不在用户的vostd工作区中改动; 不推送, 除非用户要求.

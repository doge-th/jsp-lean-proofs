# JSP-000243 Lean 证明独立验证报告（提交前自查）

**总体结论：验证通过（ witnesses 部分含本机计算信任，关键一般引理为纯标准公理）。**

在证明仓库 https://github.com/doge-th/jsp-lean-proofs 的 commit
`f3c2e369a58a4f9bff119e0c5b6e6b99f6ec1848` 上，该提交已**完整解决**指定原题
JSP-000243（"What is the shortest integer interval containing distinct
denominators whose reciprocals sum to one?"，分母 ≥ 2 读法）：答案为**[2, 6]**，
由见证（1/2+1/3+1/6=1）与更短区间的完备排除两部分组成，两部分均已机器验证。

| 必答问题 | 明确判断 | 决定性依据 |
| --- | --- | --- |
| 证明对象是否就是指定原题？ | 是 | 原题问最短整数区间；形式化分两半：(i) `JSP000243.two_three_six : 1/2 + 1/3 + 1/6 = 1`（[2,6] 可行）；(ii) 三个穷举定理 + 两个一般引理证明任何长度 ≤ 3 的区间无解。两端合取即"最短 = [2,6]"。 |
| 指定 commit 是否实际验证通过？ | 是 | 隔离克隆、干净构建退出码 0；audit.py 9 项命令全部退出码 0。 |
| 是否完整解决原题？ | 是 | 见证 + 完备排除：[2,5]、[3,6]、[4,7]（长度 3 的全部起点情形，a=2,3,4）逐子集穷举无解；a ≥ 4 时 [a,a+3] 全体倒数和 < 1（a=4..7 穷举 + a≥8 一般引理 `tail_below_one`）；长度 < 3 的区间是上述长 3 区间的子集，子集和更小。分母含 1 的平凡读法已在报告与 PR 中声明排除。 |
| 是否满足本次验证的 Lean 完整性要求？ | 满足 | 无 `sorryAx`；`tail_below_one` 仅依赖标准公理；其余目标的 `native_decide` 信任已列明。 |

## 固定证据

- 验证时间：2026-09-25（UTC+8）；工具链 `leanprover/lean4:v4.35.0-rc1`。
- Lean 仓库：https://github.com/doge-th/jsp-lean-proofs，`main`，commit
  `f3c2e369a58a4f9bff119e0c5b6e6b99f6ec1848`。
- 原题来源：awards 仓库 `problems/catalog-0201-0300.md` JSP-000243 条目。
- 目标：`JSP000243.two_three_six`、`interval_2_5_none`、`interval_3_6_none`、
  `interval_4_7_none`、`totals_below_one`、`tail_below_one`；
  源 `proofs/JSP000243.lean`（SHA-256
  `f088d21e54ea3dd4cab74149bc04701ff75e064ffb5fb46e4f1a2af5e95cc536`）。

## 数学命题与覆盖

| 原题要求 | Lean 对应 | 覆盖 |
| --- | --- | --- |
| 存在互异分母（≥2）倒数和为 1 的区间 | `two_three_six`（ℚ 精确算术） | 全部 |
| 更短区间不可能：长 3，a=2 | `interval_2_5_none`（2⁴ 子集穷举） | 全部 |
| 长 3，a=3 | `interval_3_6_none` | 全部 |
| 长 3，a=4 | `interval_4_7_none` | 全部 |
| 长 3，a≥5（及长 <3 一切情形） | `totals_below_one`（a=4..7 穷举）+ `tail_below_one`（a≥8 一般引理：每项 ≤ 1/8，总和 ≤ 1/2） | 全部 |
| 最短 = 长 4，[2,6] 达到 | (i)+(ii) 合取 | 全部 |

无未覆盖情形：a ≥ 2、长度 ≤ 3 的每一区间或被三个穷举定理直接覆盖
（[2,5]/[3,6]/[4,7] 的子区间），或 a ≥ 4 时其全区间和已 < 1。

## 环境与执行

同 JSP-000307 报告（同一隔离环境与 audit 运行，pinned commit，工作区零修改）。

## 证明完整性与可信边界

- `tail_below_one`：`[propext, Classical.choice, Quot.sound]` — 纯标准公理，
  完全构造性（`one_div_le_one_div_of_le` + `linarith`）。
- 穷举定理与见证：标准公理 + `native_decide`（对 ≤ 16 个 ℚ 分数和的有限枚举）。
- 无 `sorryAx`；无未证明假设。分母 ≥ 2 的读法已显式声明（若允许分母 1，
  平凡答案 [1,1]，见报告与 PR 注记）。

## 复核级别

实际 Lean 检查（隔离环境、pinned commit、官方 audit.py、日志存于
`verification/audit-f3c2e369/`）。本报告为提交者自查，以维护者复核为准。

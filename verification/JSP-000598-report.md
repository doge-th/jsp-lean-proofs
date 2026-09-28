# JSP-000598 Lean 证明独立验证报告（提交前自查）

**总体结论：验证通过。**

在 commit `29aff693f9f0ebb73b441837c54eea6dd18422f8` 上，官方
`skills/lean-verify/scripts/audit.py run` 对本文件全部目标返回
**`standard_axioms_only`**，公理集合恰为 [propext, Classical.choice, Quot.sound]。
本文件零 `native_decide`、零 `sorry`、零 `Nat.maxPrimeFac`；仅使用 `decide`
（内核归约）、`norm_num`、`simp`/`ac_rfl`、核心 `omega` 与 `interval_cases`。

## 题目与原题来源

- 目录：`problems/catalog-0501-0600.md`，条目 `JSP-000598`
- 对应 Erdős Problem #730（erdosproblems.com/730）
- 参考文献：Erdős–Graham–Ruzsa–Straus, *On the prime factors of (2n n)*,
  Math. Comp. **29** (1975) 83–92；目录另引 GPT-Pro 补充证明（Overleaf）

## 证明内容

| 目标 | 结论 |
|---|---|
| `jsp598_yes` | 存在 m ≠ n 使 `C(2m,m)` 与 `C(2n,n)` 素因子集合相同；见证 (87, 88) |
| `jsp598_support_87_88` | 两者支撑集恰为同一 28 元素数集（逐元素计算） |
| `jsp598_example_87_88` | EGRS 第一个例子，作为独立命题验证 |
| `jsp598_example_607_608` | EGRS 第二个例子，135 元素数支撑集 |
| `dvd_B_le` | **Kummer 界**：素数 p ∣ `C(2n,n)` ⟹ p ≤ 2n |
| `B_succ_mul` | 递推 `B(n+1)·(n+1) = B n · 2(2n+1)` |

Kummer 界是整个证明可行的技术关键：它把素因子限制在 `p ≤ 2n` 的有限范围内，
使支撑集成为内核可穷举检验的有限对象。

## 覆盖范围（明确声明，不隐藏）

已证明：目录字面问题的有限/存在性内容 + 两个已发表例子 + 支撑它们的两个一般引理。

**未证明**：目录所引 GPT-Pro 补充证明中的渐近断言——即存在正下密度的 x 使
`rad C(2n_x, n_x) = rad C(2n_x+2, n_x+1)`，等价于"存在无穷多组这样的连续数对"。
该断言是研究级解析数论论证（Kummer 进位、受限 p 进制数位集、CRT 计数、一阶矩估计，
常数 `Λ = 4C + (2/3)log 2 < 1`），需要 Mathlib 中目前不可用的实/解析机器，本文件不予主张。

## 技术说明

`Nat.choose` 的 Pascal 递归定义需要 2^87 步展开，内核无法归约。证明改用
`Nat.choose_eq_factorial_div_factorial` 重写（Mathlib 的 `Nat.factorial` 是
内核可归约的），随后以 `decide` 收尾。

## 复现

```bash
lake build JSP-000598
lake env lean <file>   # 查看 #print axioms 输出
```

本报告为提交者自查证据，不构成独立认证；以维护者复核为准。

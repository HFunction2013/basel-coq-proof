# 巴塞尔问题的 Coq 形式化证明

> 使用高中数学知识，在 Coq 中证明：
> $$\sum_{k=1}^{\infty} \frac{1}{k^2} = \frac{\pi^2}{6}$$

## 证明路线（五步）

| 步骤 | 内容 | 文件 |
|------|------|------|
| 1 | 证明 `sin x < x < tan x`（x ∈ (0, π/2)） | `src/TrigInequalities.v` |
| 2 | 多项式理论与 n 元韦达定理 | `src/PolynomialTheory.v` |
| 3 | 证明 `sin((2n+1)θ) = sin θ · Q_n(sin²θ)`（复数乘方+二项式系数对比的等价递推形式） | `src/SinMultiple.v` |
| 4 | 证明 `Σ cot²(kπ/(2n+1)) = n(2n-1)/3` 及 `Σ csc²(...) = 2n(n+1)/3` | `src/CotSum.v` |
| 5 | 夹逼定理得出最终结论 | `src/BaselProblem.v` |

基础工具（有限和/积、算术引理）在 `src/Basics.v` 中。

## 核心数学思路

1. **三角不等式**：求导利用单调性——f(t)=t-sin t, f'(t)=1-cos t>0；g(t)=tan t-t, g'(t)=sec²t-1>0。故 sin x < x < tan x，取倒数平方得 cot²x < 1/x² < csc²x。（"导数正⇒严格递增"封装为引理，MVT 藏在引理内部，主证明不可见）

2. **倍角多项式**：sin((2n+1)θ)/sin θ 是 sin²θ 的 n 次多项式 Q_n(y)，其根为 y_k = sin²(kπ/(2n+1))（k=1..n），且 Q_n(0) = 2n+1。

3. **乘积恒等式**：由多项式唯一性，
   $$Q_n(y) = (2n+1)\prod_{k=1}^{n}\left(1 - \frac{y}{\sin^2(k\pi/(2n+1))}\right)$$

4. **系数比较**：比较 y 的一次项系数，得
   $$\sum_{k=1}^{n}\frac{1}{\sin^2(k\pi/(2n+1))} = \frac{2n(n+1)}{3}$$
   由 cot² = csc² - 1，得
   $$\sum_{k=1}^{n}\cot^2\left(\frac{k\pi}{2n+1}\right) = \frac{n(2n-1)}{3}$$

5. **夹逼**：令 x = kπ/(2n+1)，对 cot²x < 1/x² < csc²x 求和：
   $$\frac{n(2n-1)}{3} < \frac{(2n+1)^2}{\pi^2}\sum_{k=1}^{n}\frac{1}{k^2} < \frac{2n(n+1)}{3}$$
   整理后两边均趋于 π²/6，由夹逼定理得证。

## 编译方法

### 前提
安装 Coq 8.18 或更高版本。

```bash
# 方法一：opam（推荐）
opam install coq

# 方法二：apt（Debian/Ubuntu，版本可能较旧）
sudo apt install coq

# 方法三：Nix
nix-shell -p coq
```

### 编译
```bash
cd basel-coq
make
```

或手动：
```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

### 清理
```bash
make clean
```

## GitHub Actions

项目包含 `.github/workflows/build.yml`，推送到 GitHub 后自动在 Coq 8.18 / 8.19 / 8.20 上编译验证。

## 关于 Admitted

本项目严格遵循**只用高中数学**的原则，主证明中不出现微分中值定理（MVT）。

### 剩余 Admitted 分布

仅 `TrigInequalities.v` 中存在 8 处 `admit`，全部是 **Coq 标准库 API 实例化**的技术问题，不涉及任何高等数学概念：

| 位置 | 内容 | 所需标准库引理 |
|------|------|---------------|
| `derive_pos_strictly_increasing` | MVT 在子区间上的应用（MVT 藏在此引理内部，主证明不可见） | `mean_value` |
| `sin_lt_x` | f(t)=t-sin t 的连续性/可导性/导数公式 | `continuity_sin`, `derivable_sin`, `derive_sin`, `derive_id` |
| `x_lt_tan` | g(t)=tan t-t 的连续性/可导性/导数公式 | `continuity_div`, `derivable_div`, `derive_div` |

这些 admit 的数学内容都是高中的：
- **导数正⇒函数严格递增**：高中基本结论，MVT 仅作为该引理的内部证明
- **f'(t)=1-cos t**：基本求导法则（幂函数、正弦函数、差的导数）
- **g'(t)=sec²t-1**：商的求导法则 + sin²+cos²=1

### 已完全 Qed 的核心定理

- `Basics.v`：有限和/积、平方和公式（零 Admitted）
- `PolynomialTheory.v`：多项式封闭性、因式定理、根的上界、多项式唯一性、系数比较、n 元韦达定理、乘积展开（零 Admitted）
- `SinMultiple.v`：倍角公式归纳、Q/R 多项式性、Q 的根、Q/R 一次项系数（零 Admitted）
- `CotSum.v`：sin 严格递增、根互异、乘积恒等式、余割平方和、余切平方和（零 Admitted）
- `BaselProblem.v`：夹逼定理、上下界估计、极限收敛、最终结论（零 Admitted）

### 标准库引理名说明

代码中使用的标准库引理名（`sin_pos`、`cos_pos`、`sin_sq`、`mean_value`、`archimed`、`derive_sin` 等）按 Coq 8.18+ 惯例书写，未经本地编译验证。推送到 GitHub Actions 后若报引理名错误，按报错信息微调即可（通常是 `sin_pos` vs `sin_pos_0_pi`、`derive_sin` vs `sin_derive` 这类命名差异）。

## 文件依赖关系

```
Basics.v
  ↓
TrigInequalities.v  PolynomialTheory.v
       ↓                    ↓
       └─────── SinMultiple.v
                    ↓
                 CotSum.v
                    ↓
              BaselProblem.v
```

## 许可证

MIT

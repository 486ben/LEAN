import numpy as np
import matplotlib.pyplot as plt
from scipy.special import jn_zeros, spherical_jn
from scipy.optimize import brentq
from math import pi

# -----------------------------
# Helper: zeros of spherical Bessel j_l
# -----------------------------
# This function finds the first n_zeros roots of spherical Bessel function j_l(x)
# 该函数用于寻找球贝塞尔函数 j_l(x) 的前 n_zeros 个零点
def spherical_bessel_zeros(l, n_zeros, x_max=None):
    zeros = []                            # store the roots / 存放零点
    x = max(1e-6, (l + 0.5) * 0.5)              # starting point, avoid zero / 初始点，避免从0开始
    step = pi * 0.9                       # scanning step, near π / 搜索步长，接近π
    if x_max is None:
        x_max = (l + n_zeros + 10) * pi         # max interval to ensure enough roots / 最大搜索区间，保证能找到足够的零点
    f_prev = spherical_jn(l, x)                 # value of spherical Bessel at current x / 当前点的球贝塞尔函数值

    while len(zeros) < n_zeros and x < x_max:   # loop until enough roots / 循环直到找到足够零点
        x_next = x + step             # move forward / 向前推进
        f_next = spherical_jn(l, x_next)      # function value at next point / 下一个点的函数值
        if f_prev * f_next < 0:          # sign change => root exists / 符号改变 => 区间内有零点

            root = brentq(lambda t: spherical_jn(l, t), x, x_next)  # numerical root finding / 数值求根
            zeros.append(root)                        # save root / 保存零点
            x = root + 1e-6                       # continue after the root / 从零点右边继续搜索
            f_prev = spherical_jn(l, x)                 # update function value / 更新函数值
        else:
            x = x_next                           # no root, keep scanning / 没有零点，继续往前
            f_prev = f_next
    return np.array(zeros)                       # return roots / 返回零点

# -----------------------------
# Cylinder eigenvalues
# -----------------------------
# This function computes Laplacian eigenvalues in a finite cylinder
# using Bessel function zeros (radial) and sine modes (axial).
# 本函数计算有限圆柱体的拉普拉斯特征值，利用贝塞尔函数零点（径向）和正弦模式（纵向）
def cylinder_eigenvalues(R=1.0, H=1.0, lam_max=5000.0):
    eigs = []                                    # store eigenvalues / 存放特征值
    m_max = int(np.sqrt(lam_max) * R) + 15                  # max angular order m / 最大角向量 m
    n_max = int(np.sqrt(lam_max) * H / pi) + 15              # max axial order n / 最大纵向模式 n

    for m in range(0, m_max+1):                        # loop over angular modes / 遍历角动量 m
        jzeros = jn_zeros(m, n_max+30)                   # get Bessel J_m zeros / 获取 J_m 的零点
        for j in jzeros:                           # loop over radial zeros / 遍历径向零点
            for n in range(1, n_max+1):                # loop over axial modes / 遍历纵向模式
                lam = (j / R)**2 + (n * pi / H)**2      # eigenvalue formula / 特征值公式
                if lam <= lam_max:                  # filter within range / 只保留在范围内
                    mult = 1 if m == 0 else 2        # multiplicity / 多重度
                    eigs.extend([lam] * mult)           # save with multiplicity / 保存并计入多重度
    return np.array(sorted(eigs))                         # return sorted eigenvalues / 返回排序结果

# -----------------------------
# Sphere eigenvalues
# -----------------------------
# This function computes Laplacian eigenvalues in a ball
# using zeros of spherical Bessel functions and spherical harmonics multiplicity.
# 本函数计算球体的拉普拉斯特征值，利用球贝塞尔函数零点和球谐函数的多重度
def sphere_eigenvalues(R=1.0, lam_max=5000.0):
    eigs = []                                    # store eigenvalues / 存放特征值
    l_max = int(np.sqrt(lam_max) * R) + 20                  # max angular momentum l / 最大角动量 l
    for l in range(0, l_max+1):                         # loop over angular modes / 遍历所有 l
        n_zeros = int(np.sqrt(lam_max) * R / pi) + 30         # required number of zeros / 需要的零点数量
        zeros = spherical_bessel_zeros(l, n_zeros)             # compute spherical Bessel zeros / 计算零点
        for a_ln in zeros:                          # loop over zeros / 遍历零点
            lam = (a_ln / R)**2                     # eigenvalue formula / 特征值公式
            if lam <= lam_max:                      # keep within range / 保留在范围内
                mult = 2*l + 1                    # multiplicity from spherical harmonics / 多重度来自球谐函数
                eigs.extend([lam] * mult)               # save with multiplicity / 保存并计入多重度
            else:
                break                           # break if exceeding limit / 超出范围则退出
    return np.array(sorted(eigs))                         # return sorted eigenvalues / 返回排序结果


# -----------------------------
# Weyl 3D: N(λ) ~ Vol(Ω) / (6 π^2) * λ^{3/2}
# -----------------------------
def weyl_3d(vol, lam_grid):
    return (vol / (6 * pi**2)) * lam_grid**1.5


# -----------------------------
# Demo parameters
# -----------------------------
R_cyl, H_cyl = 1.0, 2.0
R_sph = 1.0
lam_max = 5000.0   # <-- 放大到 5000
lam_grid = np.linspace(0, lam_max, 800)

cyl_vals = cylinder_eigenvalues(R=R_cyl, H=H_cyl, lam_max=lam_max)
sph_vals = sphere_eigenvalues(R=R_sph, lam_max=lam_max)

N_cyl = np.searchsorted(np.sort(cyl_vals), lam_grid, side='right')
N_sph = np.searchsorted(np.sort(sph_vals), lam_grid, side='right')

vol_cyl = pi * R_cyl**2 * H_cyl
vol_sph = 4/3 * pi * R_sph**3
W_cyl = weyl_3d(vol_cyl, lam_grid)
W_sph = weyl_3d(vol_sph, lam_grid)

plt.figure(figsize=(10,6))
plt.plot(lam_grid, N_cyl, label=f"Cylinder N(λ) (R={R_cyl}, H={H_cyl})", linewidth=2)
plt.plot(lam_grid, N_sph, label=f"Sphere N(λ) (R={R_sph})", linewidth=2)
plt.plot(lam_grid, W_cyl, '--', label="Weyl (cylinder)", color='C2')
plt.plot(lam_grid, W_sph, '--', label="Weyl (sphere)", color='C3')
plt.xlabel(r'$\lambda$', fontsize=14)
plt.ylabel(r'$N(\lambda)$', fontsize=14)
plt.title("Eigenvalue Counting up to λ=5000 (Cylinder vs Sphere)", fontsize=14)
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()

print("Computed counts (≤ lam_max=1000):")
print(f" Cylinder eigenvalues: {len(cyl_vals)}")
print(f" Sphere eigenvalues:   {len(sph_vals)}")

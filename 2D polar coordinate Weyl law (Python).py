#. 2D polar wey law,（2D 极坐标）

# ============================================================
# Eigenvalue counting function N(Λ) for the 2D disk (circle)
# 圆盘 Dirichlet 特征值计数函数
#
# 数学背景：
# - 分离变量得到径向方程为 Bessel 方程
# - 特征值形式： λ_{m,n} = (j_{m,n}/R)^2
#
#   其中 j_{m,n} 是 J_m(x) 的第 n 个零点
#
# - when M = 0, SOLUTION = 1 m > 0 时 SOLUTION = 2 (cos, sin) because double times the eigenvalue when they repeat
# - 重数：m=0 时 SOLUTION = 1，m > 0 时 SOLUTION = 2 (cos, sin) 因为eigenvalue可能会重复。
#
#Count eigenvalues <= lam for the Laplace-Dirichlet problem in a disk of radius R
#计算圆盘半径 R 内 Dirichlet 问题的特征值个数 (小于等于 lam)
#
#参数：
#lam : float
#给定的 Λ (截止特征值)
#R : float
#圆盘半径
#返回：
#count : int
#N(Λ) = { λ_{m,n} ≤ Λ } 的个数
# ============================================================

import numpy as np
import matplotlib.pyplot as plt
from tqdm import tqdm
from scipy.special import jn_zeros

#define a function to calculate the eigenvalue
def count_disk_eigenvalues(lam, R=1):

    count = 0
    sqrt_lam = np.sqrt(lam) # √λ = k，对应分离变量中的径向波数
    max_order = int(sqrt_lam * R) + 10  # 最大角动量量子数

    for m in range(0, max_order):   # m = 0,1,2,...
        # ------------------------------------------------------------
        # 数学：λ_{m,n} = (j_{m,n}/R)^2
        # j_{m,n} = J_m(x) 的第 n 个零点
        #
        # Code: use scipy to get Bessel function zeros
        # ------------------------------------------------------------
        # 计算贝塞尔函数零点 (足够覆盖当前λ)
        #calculate the bessel function
        num_zeros = int(sqrt_lam * R / np.pi) + 20
        zeros = jn_zeros(m, num_zeros)

        # 计数满足条件的零点
        for z in zeros:
            # λ_{m,n} = (j_{m,n}/R)^2
            eigenvalue = (z / R)**2
            if eigenvalue <= lam:
                # ------------------------------------------------------------
                # 重数: m=0 (重数1), m>0 (重数2):
                # - m=0 → only one angular solution
                # - m>0 → cos(mθ), sin(mθ) → multiplicity=2
                count += 2 if m > 0 else 1
            else:
                break
    return count

# 计算范围 (使用更小的λ范围以提高效率)

#lambda_vals_disk = np.linspace(1, 500, 50)
lambda_vals_disk = np.linspace(1, 10000, 50)

N_disk = [count_disk_eigenvalues(lam) for lam in tqdm(lambda_vals_disk)]

#red line when we need to calculate the Weyl in 2D
# N(λ) ~ Aλ/(4π) = λ/4
# Weyl 渐近线 (面积 A = πR² = π)
asymptotic_disk = np.array(lambda_vals_disk) * (np.pi/(4*np.pi))  # N(λ) ~ Aλ/(4π) = λ/4

# 绘图 draw picture
plt.figure(figsize=(12, 8))

# 原始计数
plt.plot(lambda_vals_disk, N_disk, 'b-', label=r'$N(\lambda)$ - Disk')
plt.plot(lambda_vals_disk, asymptotic_disk, 'r--', label=r'Weyl Asymptotic: $\frac{\lambda}{4}$')
plt.xlabel(r'$\lambda$')
plt.ylabel(r'$N(\lambda)$')
plt.title('Eigenvalue Counting for 2D Disk')
plt.legend()
plt.grid(True)


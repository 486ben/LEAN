#2D Retangle weyl law

import numpy as np
import matplotlib.pyplot as plt

#set a = b = 1. base case
# 矩形边长
a = b = 1.0

# Lambda range 范围
Lambda_vals = np.linspace(0, 320, 50)
#Lambda_vals = np.linspace(1, 10000, 100)

#set Λ be N(Λ) = number
N_vals = []

#Set number m and n max number.
# 上限
m_max = 50
n_max = 50

# 计算 N(λ)
for Lambda in Lambda_vals:
    count = 0
    for m in range(1, m_max):
        for n in range(1, n_max):
            #follow the paper, I calculate the follow
            #set lambda_mn formula
            #lambda is eigenvalue
            lambda_mn = np.pi**2 * ((m / a)**2 + (n / b)**2)

            # If λ_{m,n} < Λ，count N(Λ) + 1
            # 如果 λ_{m,n} < Λ，则计数 +1
            if lambda_mn < Lambda:
                count += 1

    # save the Λ(N_vals) with N(Λ)
    # 记录当前 Λ 对应的 N(Λ)
    N_vals.append(count)

#red line when we need to calculate the Weyl in 2D retangle
# 计算 Weyl 理论线：ab / (4π) * λ
Weyl_line = (a * b / (4 * np.pi)) * Lambda_vals

# 绘图
plt.figure(figsize=(10,6))
plt.plot(Lambda_vals, N_vals, label=r"$N(\lambda)$ (computed)", linewidth=2)
plt.plot(Lambda_vals, Weyl_line, 'r--', label=r"$\frac{ab}{4\pi}\lambda$ (Weyl prediction)", linewidth=2)
plt.xlabel(r"$\lambda$", fontsize=14)
plt.ylabel(r"$N(\lambda)$", fontsize=14)
plt.title("2D Rectangle", fontsize=16)
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()

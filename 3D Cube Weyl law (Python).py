#3D Cube weyl law

import numpy as np
import matplotlib.pyplot as plt

#set a = b = c = 1. base case
# 矩形边长
a = b = c = 1.0

# Lambda range 范围
#Lambda_vals = np.linspace(0, 500, 50)
Lambda_vals = np.linspace(1, 10000, 100)

#set Λ be N(Λ) = number
N_vals = []

#Set number m and n and l max number.
# 上限
m_max = 100
n_max = 100
l_max = 100

# 计算 N(λ)
for Lambda in Lambda_vals:
    count = 0
    for m in range(1, m_max):
        for n in range(1, n_max):
          for l in range(1, l_max):
            #follow the paper, I calculate the follow
            #set lambda_mnl formula
            lambda_mnl = np.pi**2 * ((m / a)**2 + (n / b)**2 + (l / c)**2)

            # If λ_{m,n,l} < Λ，count N(Λ) + 1
            # 如果 λ_{m,n,l} < Λ，则计数 +1
            if lambda_mnl < Lambda:
                count += 1

    # save the Λ(N_vals) with N(Λ)
    # 记录当前 Λ 对应的 N(Λ)
    N_vals.append(count)

#red line when we need to calculate the Weyl in 3D
# 计算 Weyl 理论线：abc / (6π^2) * λ
Weyl_line = ((a * b * c)/ (6 * (np.pi)**2 )) * Lambda_vals**(1.5)

# 绘图
plt.figure(figsize=(10,6))
plt.plot(Lambda_vals, N_vals, label=r"$N(\lambda)$ (computed)", linewidth=2)
plt.plot(Lambda_vals, Weyl_line, 'r--', label=r"$\frac{abc}{6\pi^2}\lambda^{3/2}$ (Weyl prediction)", linewidth=2)
plt.xlabel(r"$\lambda$", fontsize=14)
plt.ylabel(r"$N(\lambda)$", fontsize=14)
plt.title("3D Cube", fontsize=16)
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()

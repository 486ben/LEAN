#1D weyl law

import numpy as np
import matplotlib.pyplot as plt

# step 1
#  In 1 dimensional, because it's an interval between [0, a], so we pick an easy case and let a = 1
a = 1.0

#check the lamada , let lamada = 1 until lamada = 100.
# 取 λ 从 1 到 100 共 200 个点
# np.linspace(start, end, num)
Lambda_vals = np.linspace(0, 100, 200)

#this step is use to check how the N(lamada) is changing as lamada keep going to infinity
#这一步是为了画出 N(λ) 在多个 λ 下的取值变化。

#Set this to save the N(λ)
# 用来存每个 λ 对应的 N(λ)
N_vals = []


# use for loop to calculate each N(lamada)
# 用 for 循环来计算每个 λ 的 N(λ)
for Lambda in Lambda_vals:
    count = 0
    n = 1
    while True:
        lambda_n = (n * np.pi / a) ** 2
        # Because lambda_n = ((n pi)/(a))^2, but in our case a = 1.
        # lambda n 特征值公式

        #If lambda of n is less than the Lamada, then lamada increase 1.
        # We hope to find λ_n < Λ
        # For example, if Λ = 15, then then λ_1 = 9.87 < 15, so N(λ) = 1.
        if lambda_n < Lambda:
            count += 1  # 如果小于给定的 λ，就累计计数
            n += 1
        else:
            break
            #If lambda_n >= Lambda, then run the for loop again
            # 一旦大于等于 λ，就停止
    N_vals.append(count)
    # append
    # 将 count 加入结果列表


#--------code of draw the picture
plt.figure(figsize=(10, 6))
plt.step(Lambda_vals, N_vals, where='post', label="N(λ) (for loop version)")
plt.plot(Lambda_vals, np.sqrt(Lambda_vals)/np.pi, 'r--', label=r"$\sqrt{\lambda}/\pi$")
plt.xlabel(r"$\lambda$", fontsize=14)
plt.ylabel(r"$N(\lambda)$", fontsize=14)
plt.title("1D laplace eigenvalue picture", fontsize=16)
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.show()

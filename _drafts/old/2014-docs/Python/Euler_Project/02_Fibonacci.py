import numpy as np
import scipy as sp

"""
def Fibonacci(n): #Dreadfully inefficient, but amusing
    if n > 1:
        return Fibonacci(n-1)+Fibonacci(n-2)
    else:
        return 1


FibMatrix = np.array([
    [1,1],
    [1,0]])

print np.linalg.eigvals(FibMatrix)
print (1+np.sqrt(5))/2
    
    


for i in range (8):
    print Fibonacci(i)

"""

n1=1
n2=1
sum = 0
end =4000000
while n1 < end:
    if n1 % 2 ==0:
        sum += n1
    temp = n1
    n1 = n1 + n2
    n2 = temp

print sum
print n1

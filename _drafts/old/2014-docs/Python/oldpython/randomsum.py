import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

#randomy selects numbers in sum to do. sums from n=start to n=stop
def randomsum(f,n,start,stop):
    stop = stop + 1
    if n > (stop-start):
        n=stop-start
    Partsum = np.zeros(n)
    used = []
    used.append(np.random.randint(start,stop))
    Partsum[0]= f(used[0])
    for i in range(1, n):
        x = np.random.randint(start,stop)
        while x in used:
           # x = np.random.randint(start,stop)
            if x < stop-1:
               x = x+1
            else:
                x = np.random.randint(start,stop)
        used.append(x)
        Partsum[i]=f(x)+Partsum[i-1]
    for i in range(n):
        Partsum[i] = Partsum[i]/(i+1)*(stop-start) #averages and extrapolates to full sum
    return Partsum

def f(x):
    return np.sin(x)

def actualsum(f,start,stop):
    sum = 0
    for i in range(start,stop+1):
        sum = sum + f(i)
    return sum

start = 1
stop = 100
attempt = 100
x = range(attempt)
average = np.zeros(attempt)
for i in range(4):
    z = randomsum(f,attempt,start,stop)
    average = average + z
    plt.plot(x,z)
print "Actual Sum: " +str(actualsum(f,start, stop))
average = average/4
plt.plot(x,average)
plt.show()        


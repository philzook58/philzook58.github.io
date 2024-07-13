import numpy as np
import math


def addprime(primelist):
    guess = primelist[-1]
    notprime = True
    while notprime:
        notprime = False
        guess += 2
        for a in primelist:
            if guess % a == 0:
                notprime = True
                break
    primelist.append(guess)


end =  2000000
partsum = 0
primes = [2,3]
"""
while primes[-1] < int(sqrt(end)):
    addprime(primes)
    partsum += primes[-1]
"""

for i in range(2,end):
    prime = True
    for j in range(2,int(np.sqrt(i))+1):
        if i % j == 0:
            prime = False
            break
    if prime:
        partsum += i
       
        
print partsum


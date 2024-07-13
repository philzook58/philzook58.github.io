maxi = 20
"""
def GCD(large,small):
    if large < small:
        c = large
        large = small
        small = c
        
    a = large
    b = small
    while a != b:
        c = a - b
        if c > b:
            a = c
        else:
            a = b
            b = c
    return b

GCDlist = [1]
for i in range(1,maxi+1):
    for j in range(1,i):
        q = GCD(i,j) 
        if q not in GCDlist:
            GCDlist.append(q)

product = 1
for i in GCDlist:
    print i
    product *= i
        
print product
"""

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



def primefactors(n):
    primes = [2,3]
    factors = []
    while n > primes[-1]:
        addprime(primes)
    for i in primes:
        while n % i == 0:
            n = n/i
            factors.append(i)
    return factors

totalfactors = [2,3]
for i in range(3,maxi+1):
    temp = primefactors(i)
    for j in range(maxi+1):
        while totalfactors.count(j) < temp.count(j):
            totalfactors.append(j)
print totalfactors
product = 1
for i in totalfactors:
    product *= i
print product

for i in range(1,maxi+1):
    print product / float(i)


        


# Spearte them all into prime factors. Pick only mx number of prime factors

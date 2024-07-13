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


nthprime = 10001

primes = [2,3]
while len(primes) < nthprime:
    addprime(primes)
print primes[nthprime-1]

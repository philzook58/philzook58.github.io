factorthisdude = 600851475143

primes = [2,3]


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

factor = factorthisdude
while factor > primes[-1]:
    addprime(primes)
    while factor % primes[-1]==0:
        factor = factor/primes[-1]
        
        


    
print primes[-1]
        
    

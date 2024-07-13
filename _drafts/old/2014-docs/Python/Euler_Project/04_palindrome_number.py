maxi = 999
mini = 100

def reverse(n):
    drome = 0
    while n > 0:
        drome *= 10
        drome += n % 10
        n = n/10
    return drome

found = False

for a in range(maxi-mini):
    #print "q"
    #print a
    for b in range(0,a/2+2):
        #print b
        guess = (maxi-a+b)*(maxi-b)
        #print (maxi-a+b)
        #print (maxi-a+b)
        if guess == reverse(guess):

            print guess
            found = True
            break
    if found:
        break


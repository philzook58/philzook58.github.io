large = 378 # larger number
small = 182 # smaller number


# double check if you're a tard
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
        
print "Greatest common divisor of " + str(large) + " & " + str(small) +" is " + str(b)

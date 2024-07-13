
#This would run from now until the end of time

divisors = 0
j = 1
while divisors < 500:
    divisors = 0
    triangle = (j*(j+1))/2
    for i in range(1,triangle+1):
        if triangle % i == 0:
            divisors += 1
    j += 1
print triangle

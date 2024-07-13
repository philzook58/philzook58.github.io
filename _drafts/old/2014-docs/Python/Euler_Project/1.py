max = 999
x = 0

#The really fucking striaghtforward route
for i in range(max+1):
	if i % 3 == 0 or i % 5 == 0:
		x += i

print x

#The doable by hand route

def count(n,N):
    return N/n*(N/n+1)*n/2 #Uses n(n+1)/2 formula.

print count(3,max)+count(5,max)-count(15,max) #Number of 3 + 5 - double counting

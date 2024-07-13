

def Merge(arr1,arr2):
    #print arr1
    retarr = []
    inv = 0
    i=0
    j=0
    for n in range(len(arr1)+len(arr2)):
            if j == len(arr2):
                if type(arr1) == int:
                    retarr.append(arr1[i:])
                else:
                    retarr.extend(arr1[i:])

                #inv += (len(arr1)-i)*len(arr2)
                break
            elif i == len(arr1):
                if type(arr2) == int:
                    retarr.append(arr2[j:])
                else:
                    retarr.extend(arr2[j:])
                
               
                break
            
            elif arr2[j] < arr1[i]:
                inv += len(arr1)-i
                retarr.append(arr2[j])  
                j+= 1
            else: 
                retarr.append(arr1[i])
                i+= 1
                
    #print retarr
    return (retarr,inv)
                
            
            


def Sort(arr):
    if len(arr) <= 1:
        return (arr,0)
    else:
        (arr1,inv1) = Sort(arr[0:len(arr)/2])
        (arr2,inv2) = Sort(arr[len(arr)/2:])
        (arr3,inv3) = Merge(arr1,arr2)
        return (arr3,inv1+inv2+inv3)

f = open('integerarray.txt')
#print f

initarr=[]

#read line into array
for line in f.readlines():
	initarr.append(int(line))
#print initarr
f.close
(finarr,inversions) = Sort(initarr)
#print finarr
print inversions




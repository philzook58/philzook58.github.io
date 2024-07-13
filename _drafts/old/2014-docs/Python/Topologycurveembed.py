import numpy as np
from scipy import linalg
from mpl_toolkits.mplot3d import Axes3D
import matplotlib.pyplot as plt

length = 10
link2d = np.zeros((length,2))

#build random link
link2d[1,1] = 1
for i in range(1,length-1):
    link2d[i,:]= link2d[i-1,:] + 10*np.random.randn(2)[:]
    



    

#seal link
collisions = np.array([])
colmat = np.zeros((2,2))
colcoeff = np.zeros(2)
colvec = np.zeros(2)

for i in range(length-1):
    for j in range(i+1,length-1):
        colmat[:,0]=link2d[i+1,:]- link2d[i,:]
        colmat[:,1]=link2d[j,:]- link2d[j+1,:]
        colvec[:]=link2d[j,:]-link2d[i,:]
        #print colmat
        colcoeff[:] = linalg.solve(colmat,colvec)
        print colcoeff
        if 0 < colcoeff[0] < 1 and 0 < colcoeff[1] < 1:
            collisions = np.append(collisions,np.array([i,j]),axis=2)
print collisions
        

#Find collisions
  #array of two indices, index of top, index of bottom

"""link = np.array([
    [4,5,6],
    [7,8,9],
    [2,3,5]])

"""



fig = plt.figure()

ax = fig.gca(projection='3d')
ax.set_xlabel('X axis')
ax.set_ylabel('Y axis')
ax.set_zlabel('Z axis')
#ax.plot(link[:,0], link[:,1], link[:,2], label='parametric curve')
ax.plot(link2d[:,0], link2d[:,1], np.zeros(length), label='parametric curve')
#ax.scatter(link2d[,0], link2d[:,1], np.zeros(length), label='parametric curve')
plt.show()


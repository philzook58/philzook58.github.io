import numpy as np
import scipy as sp
from scipy import integrate
import matplotlib.pyplot as plt
import svgwrite
import os


#
#size factor
L = 20
N=5

#use coordinates for hexagonal grid (1,0), basis vectors
a = L*np.array([1.,0.])
b = L* np.array([1./2, np.sqrt(3)/2]);

offset = 10 + N*L

#print(a)
#print(b)

dwg = svgwrite.Drawing('test.svg', profile='tiny')

def coords(i,j):
    return (offset+i*a[0]+j*b[0],offset+i*a[1]+j*b[1])




#generate faces

def plotfaces():
    for i in range(-N,N):
        for j in range(-N,N):
            if(i+j+1 <= N and i+j >= -N):
                stroke=svgwrite.rgb(10, 10, 16, '%')
                dwg.add(dwg.polygon(points=[coords(i+1,j),coords(i,j+1),coords(i,j)],fill='blue'))

    for i in range(-N,N):
        for j in range(-N,N):
            if(i+j+2 <= N and i+j+1 >= -N):
                stroke=svgwrite.rgb(10, 10, 16, '%')
                dwg.add(dwg.polygon(points=[coords(i+1,j),coords(i,j+1),coords(i+1,j+1)],fill='red'))



#print( range(-2,2))


def plotvertices():
    verts = 0
    for i in range(-N,N+1):
        for j in range(-N,N+1):
            if(np.abs(i+j) <= N):
                verts = verts +1
                dwg.add(dwg.circle(coords(i,j), r=2))
    print(str(verts) + " Vertices")

#intrisinc way of doing edges: three spearate loops

'''
for i in range(-N-3,N+1):
    for j in range(-N-3,N+1):
        #if(np.abs(i+j) <= N):
            stroke=svgwrite.rgb(0, 10, 0, '%')

            if(i+1<=N and i >= -N and j <= N and j>=-N and j+i+1<= N and i+j>= -N):
                dwg.add(dwg.line(start=coords(i,j), end=coords(i+1,j),stroke=stroke))

            if(i<=N and i >= -N and j+1 <= N and j>=-N and j+i+1<= N and i+j>= -N):
                dwg.add(dwg.line(start=coords(i,j), end=coords(i,j+1),stroke=stroke))

            if(i+1<=N and i >= -N and j+1 <= N and j>=-N and j+i+1<= N and i+j+1>= -N):
                dwg.add(dwg.line(start=coords(i+1,j), end=coords(i,j+1),stroke=stroke))
'''

def plotedges():
    for i in range(-N,N):
        for j in range(-N,N+1):
            if(i+j+1 <= N and i+j >= -N):
                stroke=svgwrite.rgb(0, 10, 0, '%')
                dwg.add(dwg.line(start=coords(i,j), end=coords(i+1,j),stroke=stroke))

    for i in range(-N,N+1):
        for j in range(-N,N):
            if(i+j+1 <= N and i+j >= -N):
                stroke=svgwrite.rgb(0, 10, 1, '%')
                dwg.add(dwg.line(start=coords(i,j), end=coords(i,j+1),stroke=stroke))

    for i in range(-N,N):
        for j in range(-N,N):
            if(i+j+1 <= N and i+j+1 >= -N):
                stroke=svgwrite.rgb(0, 10, 1, '%')
                dwg.add(dwg.line(start=coords(i+1,j), end=coords(i,j+1),stroke=stroke))



plotfaces()
plotvertices()
plotedges()

#for i in range(-N,N+1):
#    print(100+i*a[1]+1*b[1])
#dwg.add(dwg.line((0, 0), (100, 100), stroke=svgwrite.rgb(10, 10, 16, '%')))
#dwg.add(dwg.text('Test', insert=(100, 100), fill='red'))
#dwg.add(dwg.circle(center=(100,100), r=4))
dwg.save()

#print(os.getcwd())

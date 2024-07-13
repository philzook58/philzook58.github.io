import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
import matplotlib



def reflect(point,line1,line2):
    normline=(line2-line1)
    normline = normline/np.linalg.norm(normline) #normalized vector lying along line
    perpline = np.array([-normline[1],normline[0]])
    relpos = point-line1
    newrelpos = relpos - 2*perpline*np.dot(relpos,perpline) #reflec about line
    return newrelpos + line1


origin = np.zeros(2)
x = np.array([1,0])
y = np.array([0,1])
v = x+y
print "Reflection of " + str(v) + " about x-axis): " +str(reflect(v,y,x))

fig=plt.figure()
ax1 = fig.add_subplot(111)
ax2 = fig.add_axes([-1,-1,1,1])
#l1 = matplotlib.lines.Line2D([0, 0], [0, 1],
       #     figure=fig)
fig.show()


"""
fig = plt.figure()

l1 = matplotlib.lines.Line2D([0, 1], [0, 1],
           transform=fig.transFigure, figure=fig)

l2 = matplotlib.lines.Line2D([0, 1], [1, 0],
           transform=fig.transFigure, figure=fig)

fig.lines.extend([l1, l2])

fig.canvas.draw()
    """

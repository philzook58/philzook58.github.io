"""
Matplotlib Animation Example

author: Jake Vanderplas
email: vanderplas@astro.washington.edu
website: http://jakevdp.github.com
license: BSD
Please feel free to use and modify this, but keep the above information. Thanks!
"""

import numpy as np
from matplotlib import pyplot as plt
from matplotlib import animation

# A demostration of usage
"""
an = Animate()
#first argument is array of x values, second is frame number
def f(x,i):
    return np.sin(2 * np.pi * (x - 0.01 * i))
x = np.linspace(0, 2, 1000)
an.movie(x, f)
""""

class Animate():

    # initialization function: plot the background of each frame
    def init(self):
        self.line.set_data([], [])
        return self.line,

    # animation function.  This is called sequentially
    def animate(self,i):
        
        y = self.func(self.x,i)
        self.line.set_data(self.x, y)
        return self.line,

    
    def movie(self, x, func, range = (-2,2)):
        self.x =  x
        self.func = func
        self.fig = plt.figure()
        self.ax = plt.axes(xlim=(x[0], x[-1]), ylim=range)
        self.line, = self.ax.plot([], [], lw=2)
        self.anim = animation.FuncAnimation(self.fig, self.animate, init_func=self.init,
                                   frames=200, interval=20, blit=True)
        plt.show()

    # save the animation as an mp4.  This requires ffmpeg or mencoder to be
    # installed.  The extra_args ensure that the x264 codec is used, so that
    # the video can be embedded in html5.  You may need to adjust this for
    # your system: for more information, see
    # http://matplotlib.sourceforge.net/api/animation_api.html
    def save(self,filename):
        self.anim.save(filename, fps=30, extra_args=['-vcodec', 'libx264'])



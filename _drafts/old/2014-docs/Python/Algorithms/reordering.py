# -*- coding: utf-8 -*-
"""
Created on Sun Jan 20 01:36:47 2013

@author: Philip
"""
import numpy as np
gridbase = 3
gridpow = 3
gridnum=gridbase**gridpow + 1
reord = np.zeros(gridnum)


reord[0]=0
reord[1]=gridnum - 1
n= 2
for i in range(gridpow):
    for j in range(gridnum):
        if(j % gridbase**(gridpow-i) != 0 and j % gridbase**(gridpow-i-1) == 0):
            print reord
            reord[n]=j
            n=n+1
            
print reord
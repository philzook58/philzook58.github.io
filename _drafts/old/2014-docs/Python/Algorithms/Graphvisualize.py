# -*- coding: utf-8 -*-
"""
Created on Mon Jan 21 13:49:00 2013

@author: Philip
"""

import networkx as nx

import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

import Matlib

#G = nx.Graph()
G = nx.DiGraph()
size = 4
G.add_nodes_from(range(size**2))
K = Matlib.K(size)
I = np.identity(size)

K2D = np.kron(K,I) + np.kron(I,K)
for i in range(size**2):
    for j in range(size**2):
        if  K2D[i,j] != 0:
            G.add_edge(i,j)
#er=nx.erdos_renyi_graph(100,0.15)
#nx.draw(er)
#nx.draw_spectral(er)
nx.draw_spring(G)
plt.show()
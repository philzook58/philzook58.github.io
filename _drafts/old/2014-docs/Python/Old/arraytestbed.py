import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


a = np.array([1,2,3,4])

b = np.hstack((np.array([0,1]),a))


lagrangemult = b[0:2]

print lagrangemult
print b

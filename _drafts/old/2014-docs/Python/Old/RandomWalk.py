import numpy as np
import scipy as sp
from matplotlib import pyplot as plt


walklength = 50
a = 1
walknumber = 10000

walks = np.zeros((walknumber,walklength))



for n in range(walknumber):
    for t in range(walklength):
        walks[n,t] = walks[n,t-1] + (-1)**np.random.randint(1,3)
    #plt.plot(walks[n,:]) #plots some walks

#Some srtatisitc of the end of the walk
average = np.sum(walks[:,-1])/walknumber
moment2 = np.sum(walks[:,-1]**2)/walknumber
variance = np.sqrt(moment2 - average**2)
predictvariance = np.sqrt(walklength-1)
print "Average = " + str(average)
print "Variance = " + str(variance)
print "Predicted Variance = " + str(predictvariance)



plt.hist(walks[:,-1],bins=70) #Histogram of the end of the walk


plt.show()
        

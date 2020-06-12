import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns; sns.set()  
plt.rcParams['figure.figsize'] = (16, 9)
plt.style.use('ggplot')


dataset=np.loadtxt('A.txt', dtype={'names': ('v1', 'v2'),     'formats': ('f8', 'f8')} ) 


f1 = dataset['v1']
f2 = dataset['v2']
X = np.array(list(zip(f1, f2)))



from sklearn.cluster import KMeans
wcss = []
for i in range(1,100):
    km=KMeans(n_clusters=i,init='k-means++', max_iter=300, n_init=1, random_state=0)
    km.fit(X)
    wcss.append(km.inertia_)
plt.plot(range(1,100),wcss)
plt.title('Convergence Curve')
plt.xlabel('Number of iterations')
plt.ylabel('SSE')
plt.show()
    

import pylab as pl1
from sklearn.decomposition import PCA
for k in range (1, 11):
    kmeans_model = KMeans(n_clusters=k, random_state=1).fit(X)
    labels = kmeans_model.labels_
    interia = kmeans_model.inertia_
    print ("k:",k, " SSE:", interia)
print()

km3=KMeans(n_clusters=3,init='k-means++', max_iter=300, n_init=10, random_state=0)
y_means = km3.fit_predict(X)



plt.scatter(X[y_means==0,0],X[y_means==0,1],s=50, c='black',label='Cluster1')
plt.scatter(X[y_means==1,0],X[y_means==1,1],s=50, c='blue',label='Cluster2')
plt.scatter(X[y_means==2,0],X[y_means==2,1],s=50, c='green',label='Cluster3')


plt.scatter(km3.cluster_centers_[:,0], km3.cluster_centers_[:,1],s=200,marker='s', c='red', alpha=0.7, label='Centroids')
plt.title('Clustering results for K=3')
plt.xlabel('X-axis')
plt.ylabel('Y-axis')
plt.legend()
plt.show()



plt.scatter(X[y_means==0,0],X[y_means==0,1],s=50, c='purple',label='Cluster1')
plt.scatter(X[y_means==1,0],X[y_means==1,1],s=50, c='blue',label='Cluster2')
plt.scatter(X[y_means==2,0],X[y_means==2,1],s=50, c='green',label='Cluster3')
plt.scatter(X[y_means==3,0],X[y_means==3,1],s=50, c='cyan',label='Cluster4')
plt.scatter(X[y_means==4,0],X[y_means==4,1],s=50, c='magenta',label='Cluster5')
plt.scatter(X[y_means==5,0],X[y_means==5,1],s=50, c='orange',label='Cluster6')

plt.scatter(km.cluster_centers_[:,0], km.cluster_centers_[:,1],s=200,marker='s', c='red', alpha=0.7, label='Centroids')
plt.title('Clustering results')
plt.xlabel('X-axis')
plt.ylabel('Y-axis')
plt.legend()
plt.show()


import scipy.cluster.hierarchy as sch
dend=sch.dendrogram(sch.linkage(X, method='ward'))
plt.title("Dendrogram")
plt.xlabel('Data')
plt.ylabel('Cluster')
plt.show()




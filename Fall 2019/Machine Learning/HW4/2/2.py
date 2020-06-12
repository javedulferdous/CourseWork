import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from sklearn.cluster import AgglomerativeClustering
import scipy.cluster.hierarchy as sch
from scipy.spatial import distance_matrix
from scipy.spatial.distance import cdist 

dataset=np.loadtxt('B.txt', dtype={'names': ('v1', 'v2'),     'formats': ('f8', 'f8')} ) 


f1 = dataset['v1']
f2 = dataset['v2']
X = np.array(list(zip(f1, f2)))

single = AgglomerativeClustering(n_clusters=4, affinity='euclidean', linkage='single')
complete = AgglomerativeClustering(n_clusters=4, affinity='euclidean', linkage='complete')
average = AgglomerativeClustering(n_clusters=4, affinity='euclidean', linkage='average')


complete_predict = complete.fit_predict(X)
average_predict = average.fit_predict(X)
single_predict = single.fit_predict(X)


plt.scatter(X[single_predict==0,0],X[single_predict==0,1],s=100, c='red')
plt.scatter(X[single_predict==1,0],X[single_predict==1,1],s=100, c='blue')
plt.scatter(X[single_predict==2,0],X[single_predict==2,1],s=100, c='green')
plt.scatter(X[single_predict==3,0],X[single_predict==3,1],s=100, c='yellow')
plt.title('MIN')
plt.legend(['Cluster 1','Cluster 2','Cluster 3'])
plt.show()

plt.scatter(X[complete_predict==0,0],X[complete_predict==0,1],s=100, c='red')
plt.scatter(X[complete_predict==1,0],X[complete_predict==1,1],s=100, c='blue')
plt.scatter(X[complete_predict==2,0],X[complete_predict==2,1],s=100, c='green')
plt.scatter(X[complete_predict==3,0],X[complete_predict==3,1],s=100, c='yellow')
plt.title('MAX')
plt.legend(['Cluster 1','Cluster 2','Cluster 3'])
plt.show()

plt.scatter(X[average_predict==0,0],X[average_predict==0,1],s=100, c='red')
plt.scatter(X[average_predict==1,0],X[average_predict==1,1],s=100, c='blue')
plt.scatter(X[average_predict==2,0],X[average_predict==2,1],s=100, c='green')
plt.scatter(X[average_predict==3,0],X[average_predict==3,1],s=100, c='yellow')
plt.title('Average')
plt.legend(['Cluster 1','Cluster 2','Cluster 3'])
plt.show()


Cluster_Centers=X.copy()
Clusters=np.array([i for i in range(Cluster_Centers.shape[0])]).reshape(Cluster_Centers.shape[0],1)
Clusters={}
for i in range(X.shape[0]):
    Clusters[i]=X[i]

HistoryCentroid=np.array([])
HistoryED=np.array([])
Cluster_Centers=Cluster_Centers[np.argsort(np.sum(Cluster_Centers**2,axis=1))]

while Cluster_Centers.shape[0]!=1:
    dist=np.tril(distance_matrix(Cluster_Centers,Cluster_Centers))
    indices=np.where(dist==np.min(dist[dist!=0]))[0]
    if type(indices)==np.ndarray:
        i1=indices[0]
        i2=np.where(dist==np.min(dist[dist!=0]))[1][0]
    else:
        i1=int(np.where(dist==np.min(dist[dist!=0]))[0])
        i2=int(np.where(dist==np.min(dist[dist!=0]))[1])
        
    if i1>i2:
        i1,i2=i2,i1
        
    ed=np.min(dist[dist!=0])
    c1=0
    c2=0
   
    if Cluster_Centers[i1].tolist() in HistoryCentroid.tolist():
        pos=HistoryCentroid.tolist().index(Cluster_Centers[i1].tolist())
        c1=HistoryED[pos]
        
    if Cluster_Centers[i2].tolist() in HistoryCentroid.tolist():
        pos=HistoryCentroid.tolist().index(Cluster_Centers[i2].tolist())
        c2=HistoryED[pos]
    
    if HistoryCentroid.size==0:
        HistoryCentroid=np.hstack((HistoryCentroid,(Cluster_Centers[i1]+Cluster_Centers[i2])/(2)))
        HistoryED=np.hstack((HistoryED,ed))
    else:
        HistoryCentroid=np.vstack((HistoryCentroid,(Cluster_Centers[i1]+Cluster_Centers[i2])/(2)))
        HistoryED=np.vstack((HistoryED,ed))
    
    
    
   
    p1=np.sqrt(np.sum(Cluster_Centers[i1]**2))
    p2=np.sqrt(np.sum(Cluster_Centers[i2]**2))
    
    Cluster_Centers[i1]=(Cluster_Centers[i1]+Cluster_Centers[i2])/(2)
    Cluster_Centers=np.delete(Cluster_Centers,i2,axis=0)
   
    
    plt.plot([p1,p1,p2,p2],[c1,ed,ed,c2])
plt.show()


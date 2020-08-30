import numpy as np
import lmdb
import caffe

N = 1000

X = np.zeros((N, 3, 32, 32), dtype = np.uint8)
y = np.zeros(N, dtype = np.int64)

map_size = X.nbytes * 10

env = lmdb.open('mylmdb', map_size=map_size)

with env.begin(write=True) as txn:
    # txn is a Transaction object
    for i in range(N):
        datum = caffe.proto.caffe_pb2.Datum()
        datum.channels = X.shape[1]
        datum.height = X.shape[2]
        datum.width = X.shape[3]
        datum.data = X[i].tobytes()
        datum.label = int(y[i])
        str_id = '{:08}'.format(i)
        txn.put(str_id.encode('ascii'), datum.SerializeToString())
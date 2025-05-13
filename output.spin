int i = 1;
do
    :: (i>n) -> break
    :: else -> i++;
od
typedef node {
    int value;
}
node node_mem[9];
int node_valid[9];
node n[10];

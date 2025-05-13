struct node {
    struct node *next;
    int value;
};

struct node* tail;
void test( struct node *temp){
    tail->next = temp;
    tail = temp;
}
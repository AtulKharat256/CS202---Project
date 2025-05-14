#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(){
int x = 0, a = 1, b = 2;

switch(x) {
    case 0:
        a++;
        b++;
        break;
    case 1:
        a--;
        b--;
        break;
    default:
        break;
}
}

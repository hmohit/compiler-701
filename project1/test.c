#include <stdio.h>
#include <stdlib.h>

void emptyFunction(){
    printf("Function did bugger all\n");
}

int main(int argc, char **argv){
    int variable1 = 0;
    int variable2 = 3;
    int variable3 = variable1 + variable2;
    printf("Answer: %d\n", variable3);
    emptyFunction();
    return 0;
}




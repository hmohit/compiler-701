#include <stdio.h>

int main( int argc,char** argv )
{
  
  int SWITCH=0;
  int x,y;
  int REACH=0;
  x=0;y=0;
  while (SWITCH < 4) {
    switch(SWITCH){
    case 0:
      REACH=6;
      break;
    case 1:
      x=SWITCH;
      break;
    case 2:
      REACH=7;
      SWITCH = SWITCH;
      break;
    }
    if(x){
      REACH=9;
    }else if(y){
      REACH=0;
    }else if(REACH==0){
      x=y++;
    }else
      y=5;

    x = x;
    printf(" %d %d %d %d\n",x ,y,SWITCH,REACH);
    SWITCH++;
  }
}

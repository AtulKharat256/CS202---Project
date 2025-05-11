i = 0;
do
    :: ( i < 3) ->
        j = 0;
        do
            :: (j < 2) ->
                arr[i][j] = i + j;
                j++;
            :: else -> break;
        od;
    :: else -> break;
od;

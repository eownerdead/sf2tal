#include <inttypes.h>
#include <stdio.h>


int64_t	sf2talMain(void);


int
main(void)
{
	int64_t v = sf2talMain();
        printf("%" PRId64 "\n", v);

        return 0;
}

CC = gcc
CFLAGS = -O3 -march=native -std=c11 -Wall -Wextra

petersen: petersen.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# MAXM=5 build for the m=5 cases (petersen_39/50): smaller heap
# nodes (32 bytes) for the best-first campaign.  Refuses m > 5 cases.
petersen5: petersen.c
	$(CC) $(CFLAGS) -DMAXM=5 -o $@ $< -lm

clean:
	rm -f petersen petersen5

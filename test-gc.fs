\ test GC word-by-word

\ these tests interact, so better add new ones at the end

s" compat/required.fs" included \ required
s" compat/assert.fs" required \ assert2( assert3( assert-level

2 assert-level !

100000 true false s" gc.fs" included drop 2drop
s" tester.fs" included
decimal

also garbage-collector
cr


{ 0 log2 -> 0 }
{ 3 log2 -> 1 }
{ 4 log2 -> 2 }
{ 7 log2 -> 2 }
{ 8 log2 -> 3 }

{ 0 bit-addr -> 0 0 }
{ 1 bit-addr -> 1 0 }
{ 31 bit-addr -> 31 0 }
{ 1 0 addr-bit -> 1 }

: test-bitaddr ( -- )
    1000 0 ?do
	i bit-addr aligned addr-bit i <> abort" test-bitaddr failed"
    loop ;

{ test-bitaddr -> }

{ 1 0 1 bit-addr-mask -> 2 0 }

: test-bit-addr-mask ( -- )
    1000 0 ?do
	i 0 1 bit-addr-mask
	over 0= abort" test-bit-addr-mask 0= failed"
	aligned swap log2 swap addr-bit
	i <> abort" test-bit-addr-mask failed"
    loop ;

{ test-bit-addr-mask -> }

create testbv 10 cells allot

{ testbv 10 cells erase -> }
{ 2 testbv set-bit -> }
{ 31 testbv set-bit -> }
{ 32 testbv set-bit -> }
{ 63 testbv set-bit -> }
{ 64 testbv set-bit -> }
{ 0 testbv bit-set? -> false }
{ 1 testbv bit-set? -> false }
{ 2 testbv bit-set? -> true }
{ 3 testbv bit-set? -> false }
{ 30 testbv bit-set? -> false }
{ 31 testbv bit-set? -> true }
{ 32 testbv bit-set? -> true }
{ 33 testbv bit-set? -> false }
{ 62 testbv bit-set? -> false }
{ 63 testbv bit-set? -> true }
{ 64 testbv bit-set? -> true }
{ 65 testbv bit-set? -> false }

{ 1 first-bit -> 0 }
{ 2 first-bit -> 1 }
{ 3 first-bit -> 0 }
{ 4 first-bit -> 2 }

: test-first-bit ( -- )
    cell-bits 0 ?do
	1 i lshift first-bit i <> abort" test-first-bit 1 failed"
	-1 i lshift first-bit i <> abort" test-first-bit -1 failed"
    loop ;

{ test-first-bit -> }

{ 4 testbv set-bit -> }
{ 7 testbv set-bit -> }
{ 8 testbv set-bit -> }
{ 31 testbv set-bit -> }
{ 32 testbv set-bit -> }
{ 63 testbv set-bit -> }
{ 64 testbv set-bit -> }
{ 192 testbv set-bit -> }
{ 0 testbv find-next-bit -> 2 }    
{ 3 testbv find-next-bit -> 4 }    
{ 5 testbv find-next-bit -> 7 }    
{ 8 testbv find-next-bit -> 8 }    
{ 9 testbv find-next-bit -> 31 }    
{ 32 testbv find-next-bit -> 32 }    
{ 33 testbv find-next-bit -> 63 }    
{ 64 testbv find-next-bit -> 64 }    
{ 65 testbv find-next-bit -> 192 }

variable testv 5 testv !
{ 3 testv and! -> }
{ testv @ -> 1 }

: test-clear-bits
    10 cell-bits * 0 do
	testbv 10 cells -1 fill \ !! env dependences
	i 2/ i testbv clear-bits
	i 2/ 0> if
	    assert( i 2/ 1- testbv bit-set? )
	endif
	assert( i 2/ testbv find-next-bit i = )
    loop ;

{ test-clear-bits -> }

: test-grain-num-addr-num ( -- )
    1000 0 ?do
	assert( i grain-num-addr memory-block @ i grain * + = )
	assert( i grain-num-addr grain-addr-num i = )
    loop ;

{ test-grain-num-addr-num -> }

{ memory-block @ 1024 grain * + allocate-grain-info constant testgv -> }

: test-set-grain-set? ( -- )
    1024 0 do
	memory-block @ i grain * +
	assert( dup testgv grain-set? 0= )
	dup testgv set-grain
	assert( dup testgv grain-set? )
	drop
    loop ;

{ test-set-grain-set? -> }
{ testgv free -> 0 }

{ variable testlist 0 testlist ! -> }
{ list% %allot dup testlist insert-node testlist @ = -> true }
{ testlist @ list-next @ -> 0 }
{ testlist delete-node -> }
{ testlist @ -> 0 }

{ memory-block-end @ allocate-grain-info live ! -> }
{ memory-block @ border @ set-grain -> }
{ memory-block @ grain + border @ set-grain -> }
{ memory-block @ live @ set-grain -> }
{ memory-block-end @ border @ set-grain -> }
{ memory-block-end @ live @ set-grain -> }
{ memory-block-end @ active-end ! -> }

{ 0 mark? -> false }
{ memory-block @ grain - mark? -> false }
{ memory-block @ 1+ mark? -> grain 1 = }
{ memory-block @ mark? -> false }
{ memory-block @ grain + mark? -> true }
{ memory-block @ grain 2* + mark? -> false }
{ memory-block @ active-end ! -> }
{ memory-block @ grain + mark? -> false }

{ live @ free -> 0 }

\ prepare for testing mark
{ 3 grain * constant node -> }
{ node 1 cells - constant lastcell -> }
{ memory-block @ 200 node * 2dup erase + active-end ! }
{ 0 200 3 * 2 + border @ clear-bits -> }

variable list1
variable list2

: make-lists ( -- )
    \ make two lists: the first runs forward and has the Next pointer
    \ in the first cell; the second runs backwards and has the Next
    \ pointer in the last cell they are not properly terminated, but
    \ that should not play a role in this test (the respective last
    \ pointers are outside the active area). The second list has
    \ self-references in the first cell (to check whether mark can
    \ handle cycles).
    memory-block @
    dup list1 !
    100 0 do
	dup border @ set-grain
	dup node + node + over ! \ next pointer
	node +
	dup border @ set-grain
	dup node - node - over lastcell + ! \ next pointer
	dup dup ! \ self-reference
	node +
    loop
    dup border @ set-grain 
    node - list2 ! ;

\ make a copy for checking after marking
{ make-lists -> }

{ node 200 * allocate throw constant listcopy -> }
{ memory-block @ listcopy node 200 * move -> }

: test-mark ( f -- )
    100 0 do
	assert( i 2* 3 * live @ bit-set? over = )
	assert( i 2* 1+ 3 * live @ bit-set? over <> )
    loop
    drop ;

{ active-end @ allocate-grain-info live ! -> }
{ list1 @ mark -> }
{ true test-mark -> }
{ 0 200 3 * live @ clear-bits -> }
{ list2 @ mark -> }
{ false test-mark -> }

{ 0 200 3 * live @ clear-bits -> }
{ list1 @ mark-stack -> list1 @ }
{ true test-mark -> }

{ list1 rootlist% %size allocate throw tuck rootlist-addr !
  other-roots insert-node -> }
{ 0 200 3 * live @ clear-bits -> }
{ mark-others -> }
{ true test-mark -> }

{ 0 200 3 * live @ clear-bits -> }
{ mark-all -> }
{ true test-mark -> }

{ listcopy 200 node * memory-block @ over compare -> 0 }

{ active-end @ grain-addr-num set-sweep-sentinel -> }
{ 0 sweep-live -> 3 }
{ 6 sweep-live -> 9 }
{ list2 @ mark -> }
{ 0 sweep-live -> active-end @ grain-addr-num 1+ }

{ 0 200 3 * live @ clear-bits -> }
{ mark-all -> }
{ true test-mark -> }
{ 1 border @ set-bit }
{ 0 3 one-chunk -> }
{ 1 border @ bit-set? -> false }

{ 3 6 erase-chunk -> }
{ memory-block @ node + @ -> 0 }
{ memory-block @ node 2* + 1 cells - @ -> 0 }

{ freelist-sentinel freelists ! -> }
{ 3 6 free-chunk -> }
{ grain freelists freelist-search nip
  dup freelist-size @ swap freelist-list @
  -> node memory-block @ node + }
{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }

{ 0 live-grains ! -> }
{ 0 200 3 * sweep1 -> }
{ live-grains @ -> 100 3 * }
{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }

{ 0 200 3 * live @ clear-bits -> }
{ listcopy memory-block @ 200 node * move -> }
{ memory-block @ 200 node * + active-end ! -> }
{ list2 @ mark -> }
{ 0 live-grains ! -> }
{ 0 200 3 * sweep1 -> }
{ live-grains @ -> 100 3 * 1+ }
{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }

{ 0 200 3 * live @ clear-bits -> }
{ listcopy memory-block @ 200 node * move -> }
{ memory-block @ 200 node * + active-end ! -> }
{ list2 @ mark-all drop -> }
{ 0 live-grains ! -> }
{ 0 200 3 * sweep1 -> }
{ live-grains @ -> 200 3 * 1+ }
{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }

{ 0 200 3 * live @ clear-bits -> }
{ listcopy memory-block @ 200 node * move -> }
{ memory-block @ 200 node * + active-end ! -> }
{ 0 live-grains ! -> }
{ 0 200 3 * sweep1 -> }
{ live-grains @ -> 0 }
{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }

{ 200 3 * dup sweep1 -> }
{ live-grains @ -> 1 }

{ 0 200 3 * live @ clear-bits -> }
{ make-lists -> }
{ memory-block @ 200 node * + active-end ! -> }
{ 0 live-grains ! -> }
{ mark-all -> }
{ 0 200 3 * sweep1 -> }
{ live-grains @ -> 100 3 * }
{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }

{ live @ free -> 0 }
{ listcopy memory-block @ 200 node * move -> }
{ memory-block @ 200 node * + active-end ! -> }
{ collect-garbage -> }
{ live-grains @ -> 300 }
{ collect-garbage -> }
{ live-grains @ -> 301 }
{ collect-garbage -> }
{ live-grains @ -> 301 }

\ alloc stuff
{ node grain + alloc-freelist -> 0 gc-out-of-memory }
{ node alloc-freelist nip -> 0 }
{ grain alloc-freelist grain alloc-freelist
  0= rot 0= and rot grain + rot = and -> true }

{ active-end @ 10 grains + current-limit ! -> }
{ active-end @ border @ set-grain -> }  
{ 11 grains alloc-end nip -> gc-out-of-memory }
{ active-end @ 3 grains alloc-end rot rot = -> 0 true }
{ 8 grains alloc-end nip -> gc-out-of-memory }
{ active-end @ 7 grains alloc-end rot rot = -> 0 true }
{ 1 grains alloc-end nip -> gc-out-of-memory }

{ active-end @ 10 grains + current-limit ! -> }
{ node alloc-nocollect nip -> 0 }
{ active-end @ node grain + alloc-nocollect rot rot = -> 0 true }
{ 10 grains alloc-nocollect nip -> gc-out-of-memory }

{ active-end @ 10 grains alloc-extend rot rot = -> 0 true }

{ active-end @ 10 grains + current-limit ! -> }
{ 1 alloc nip -> 0 }
{ active-end @ node grain + alloc rot rot = -> 0 true }
{ 100 grains alloc -> active-end @ 100 grains - 0 }
{ current-limit @ -> memory-block-end @ }

{ freelists @ free-freelists -> }
{ freelist-sentinel freelists ! -> }


\ freelist management
{ grain freelists freelist-search
  dup rot @ = swap freelist-sentinel = -> true true }

\ never mind the sizes here, freelist management only uses the first
\ cell of each chunk
{ memory-block @ grain 2* insert-free-chunk -> }
{ memory-block @ grain + grain insert-free-chunk -> }
{ memory-block @ grain 2 * + grain 4 * insert-free-chunk -> }
{ memory-block @ grain 3 * + grain 2* insert-free-chunk -> }
{ grain freelists freelist-search nip
  dup freelist-size @ swap freelist-list @
  -> grain memory-block @ grain + }
{ grain 3 * freelists freelist-search nip
  dup freelist-size @ swap freelist-list @
  -> grain 4 * memory-block @ grain 2* + }
{ grain 5 * freelists freelist-search nip freelist-sentinel = -> true }

{ grain 2 * freelists freelist-search take-free-chunk
  -> memory-block @ grain 3 * + }
{ grain 2 * freelists freelist-search take-free-chunk
  -> memory-block @ }
{ grain 2 * freelists freelist-search nip
  dup freelist-size @ swap freelist-list @
  -> grain 4 * memory-block @ grain 2* + }

{ freelists @ free-freelists -> }

\ set by initgc
\ { current-limit @ -> memory-block-end @ }

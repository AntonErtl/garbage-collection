\ a global test of GC reused as benchmark

\ usage: time gforth -e 1 bench-gc.fs -e bye

dup constant benchmode

benchmode 1 = [if] cr .( GC with default tuning ) cr [then]
benchmode 2 = [if] cr .( using alloc-nocollect and free-chunk ) cr [then]
benchmode 3 = [if] cr .( using allocate and free ) cr [then]
benchmode 4 = [if] cr .( GC tuned for no collection ) cr [then]
benchmode 5 = [if] cr .( using allocate ) cr [then]
benchmode 6 = [if] cr .( using allot ) cr [then]

s" compat/required.fs" included \ required
s" compat/assert.fs" required \ assert2( assert3( assert-level

0 assert-level !
15000000 true false s" gc.fs" included drop 2drop
benchmode 4 = benchmode 2 = or [if]
also garbage-collector
15000000 grain/ size-offset !
set-current-limit
previous
[then]

variable seed

: initiate-seed ( -- )  74755 seed ! ;
: random  ( -- n )  seed @ 1309 * 13849 + 65535 and dup seed ! ;

struct
    cell% field list-next
    cell% field list-val
end-struct intlist%

also garbage-collector
: alloc-list ( intlist1 n1 n2 -- intlist2 )
    \ prepend intlist nodes with values between n1 and n2 to intlist1
    1+ swap ?do
	intlist% %size random 63 and +
	[ benchmode 1 = benchmode 4 = or ] [if]	alloc throw [then]
	[ benchmode 2 = ] [if] grain nalign dup alloc-nocollect throw tuck + border @ set-grain [then]
	[ benchmode 3 = benchmode 5 = or ] [if] allocate throw [then]
	[ benchmode 6 = ] [if] here swap grain nalign allot [then]
	i over list-val !
	tuck list-next !
    loop ;

: check&free-list ( intlist -- )
    \ checks that list contains nodes with values from n to 1, 2|n
    \ eliminates all odd nodes, halves the value of the others
    dup list-val @ begin ( intlist n )
	over
    while
	assert( over list-val @ over = )
	assert( over list-val @ 1 and 0= )
	over list-val dup @ 2/ swap !
	>r dup list-next @
	assert( dup )
	assert( r@ 1- over list-val @ = )
	[ benchmode 2 4 within ] [if]
	    dup >r list-next @ dup rot list-next ! r>
	    [ benchmode 2 = ] [if]
		grain-addr-num dup 1+ border @ find-next-bit free-chunk
	    [else]
		free throw
	    [then]
	[else]
	    list-next @ dup rot list-next !
	[then]
	r> 2 -
    repeat
    2drop ;
previous

: testgc ( -- intlist )
    0 1 1000 alloc-list
    500 0 ?do
	dup check&free-list
	501 1000 alloc-list
    loop ;

testgc
drop

also garbage-collector
cr .( statistics: )
cr .( live  : ) live-grains @ grains u.
cr .( active: ) active-end @ memory-block @ - u.
cr .( limit : ) current-limit @ memory-block @ - u. cr
previous

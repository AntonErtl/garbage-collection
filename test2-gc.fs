\ a global test of GC

s" compat/required.fs" included \ required
s" compat/control.fs" required \ endif ?dup-if
s" compat/assert.fs" required \ assert2( assert3( assert-level

dup assert-level ! \ comment out for benchmarking

s" compat/struct.fs" included \ not needed for Gforth >=0.4

variable seed

: initiate-seed ( -- )  74755 seed ! ;
: random  ( -- n )  seed @ 1309 * 13849 + 65535 and dup seed ! ;

struct
    cell% field list-next
    cell% field list-val
    char% 0 * field list-content
end-struct intlist%

: bounds ( addr u -- end-addr addr )
    over + swap ;

: filled? ( addr u c -- f )
\ is addr u filled with c?
    true 2swap
    bounds ?do ( c f )
	over i c@ = and
    loop
    nip ;

: check-list ( intlist -- )
    dup if
	dup list-val @ begin ( intlist n )
	    assert( over list-val @ over = )
	    assert( over list-content dup c@ dup [char] @ - swap filled? )
	    swap list-next @ swap 1-
	    over 0= until
	assert( dup 0= )
	drop
    endif
    drop ;
	

100000 cells true false s" gc.fs" included drop 2drop
also garbage-collector
2 1 size-factor 2!
100 size-offset !
set-current-limit
previous


: alloc-list ( intlist1 n1 n2 -- intlist2 )
    \ prepend intlist nodes with values between n1 and n2 to intlist1
    1+ swap ?do ( intlist )
	random 63 and 1+ dup chars intlist% %size + alloc throw ( intlist chars addr )
	i over list-val !
	dup list-content rot dup [char] @ + fill
	tuck list-next ! 
	assert2( dup check-list true )
    loop ;

: check&free-list ( intlist -- )
    \ checks that list contains nodes with values from n to 1, 2|n
    \ eliminates all odd nodes, halves the value of the others
    dup list-val @ begin ( intlist n )
        assert2( over check-list true )
	over
    while
	assert( over list-val @ over = )
	assert( over list-val @ 1 and 0= )
	over list-val dup @ 2/ swap !
	>r dup list-next @
	assert( dup )
	assert( r@ 1- over list-val @ = )
	list-next @ dup rot list-next !
	r> 2 -
    repeat
    2drop ;

: testgc ( -- intlist )
    0 1 1000 alloc-list
    500 0 ?do
	dup check-list
	dup check&free-list
	dup check-list
	501 1000 alloc-list
    loop ;

testgc
collect-garbage
drop

also garbage-collector
cr .( statistics: )
cr .( live  : ) live-grains @ grains u.
cr .( active: ) active-end @ memory-block @ - u.
cr .( limit : ) current-limit @ memory-block @ - u.
previous

\ memory allocation with automatic storage reclamation (garbage collection)

\ Copyright (C) 1998,1999 M. Anton Ertl

\ gc.fs is free software; you can redistribute it and/or
\ modify it under the terms of the GNU General Public License
\ as published by the Free Software Foundation; either version 2
\ of the License, or (at your option) any later version.

\ This program is distributed in the hope that it will be useful,
\ but WITHOUT ANY WARRANTY; without even the implied warranty of
\ MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
\ GNU General Public License for more details.

\ You should have received a copy of the GNU General Public License
\ along with this program; if not, write to the Free Software
\ Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


\ stack effect of loading this file:
\ f-deep-stacks -- f-deep-stacks

\ environmental dependences:
\ case insensitivity
\ 2's complement arithmetic
\ aus, and cells have sizes (in bits) that are powers of 2
\ floats and dfloats have alignments (in aus) that are powers of 2

\ The program uses the following words (with f-deep-stacks=true)
\ from CORE :
\ 0= : swap >r dup 2dup r> rot move ; cells r@ @ over ! cell+ 2! BEGIN
\ WHILE 2@ IF drop 2drop EXIT THEN REPEAT ELSE Variable 1- + invert
\ and DOES> immediate Create , chars aligned 2* here - allot POSTPONE
\ ?dup +! > u< [ ] Literal emit bl type [char] rshift 1+ environment?
\ Constant lshift or 2/ i LOOP 2swap = max recurse +LOOP UNTIL depth *
\ */ [']
\ from CORE-EXT :
\ true 2>r 2r@ 2r> tuck pick nip u> parse 0<> ?DO erase within false <> AGAIN 
\ from BLOCK-EXT :
\ \ 
\ from DOUBLE :
\ 2Constant 2Variable 
\ from EXCEPTION :
\ throw catch 
\ from EXCEPTION-EXT :
\ abort" 
\ from FILE :
\ S" included ( 
\ from FLOAT :
\ faligned floats 
\ from FLOAT-EXT :
\ dfaligned dfloats sfaligned sfloats 
\ from MEMORY :
\ allocate free 
\ from SEARCH :
\ Forth-wordlist search-wordlist wordlist get-order set-order
\ get-current definitions set-current
\ from SEARCH-EXT :
\ also previous 
\ from STRING :
\ compare SLiteral 
\ from TOOLS-EXT :
\ [IF] [THEN] [ELSE] CS-ROLL 

\ !! alloc does not CATCH everything (e.g. no throws from alloc-nocollect).

S" gforth" environment? 0= [if]
s" compat/required.fs" included \ required
s" compat/struct.fs" required \ struct etc.
s" compat/control.fs" required \ endif ?dup-if
s" compat/vocabulary.fs" required \ vocabulary
s" compat/exception.fs" required \ exception
s" compat/assert.fs" required \ assert2( assert3( assert-level
[else] 2drop [then]

get-current
vocabulary garbage-collector also garbage-collector definitions

\ gc allocates one very large memory block, but uses only a part of it
\ (if possible), to keep its physical memory requirements reasonable.

variable memory-block      \ address of memory block managed by gc
variable memory-block-end  \ end of memory block managed by gc
variable active-end        \ end of the part currently in use

\ ------------
\ helper words

: a> ( addr1 addr2 -- )
   u> ;

: u>= ( u1 u2 -- f )
    u< 0= ;

: u<= ( u1 u2 -- f )
    u> 0= ;

: cell- ( addr1 -- addr2 )
    [ 1 cells ] literal - ;

: CS-ROLL CS-ROLL ;

\ ---
\ I/O

variable i/o? \ true if garbage collector should show itself

: BS ( -- )
    i/o? @ if
	8 emit bl emit 8 emit
    endif ;

: (?") ( c-addr u -- )
    i/o? @ if
	2dup type
    endif
    2drop ;

: ?" ( -- ; C: "ccc<">" -- )
    [char] " parse POSTPONE sliteral POSTPONE (?") ; immediate

\ -----------------------
\ bit-vector manipulation

: log2 ( u1 -- u2 )
    \ u2=floor(ld(u1)) for u1>0, u2=0 for u1=0
    0 swap begin
	1 rshift dup
    while
	swap 1+ swap
    repeat
    drop ;

s" address-unit-bits" environment? 0= [if]
    8 \ default: an address unit is an 8-bit byte
[then]
constant address-unit-bits
address-unit-bits cells constant cell-bits \ bits per cell
cell-bits log2 constant cell-bits-shift \ dependence: cell-bits is power of 2

: bit-addr ( u1 -- u2 offset )
    \ u1=offset*au-bits+u2, u2<cell-bits
    dup [ cell-bits 1- ] literal and
    swap cell-bits-shift rshift cells ;

: addr-bit ( u1 offset -- u2 )
    \ u2=offset*au-bits+u1
    [ address-unit-bits log2 ] literal lshift + ;

: bit-addr-mask ( u1 addr1 mask1 -- mask2 addr2 )
    rot bit-addr >r lshift ( addr1 mask2; R: offset )
    swap r> + ;

: set-bit ( u addr -- )
    \ set bit u in the bitvector at addr
    1 bit-addr-mask tuck @ or swap ! ;

: bit-set? ( u addr -- f )
    \ true if bit u in bit-vector at addr is set
    1 bit-addr-mask @ and 0<> ;

: first-bit ( x -- u )
    \ u is the first set bit in x
    \ some architectures have a special instruction for this (e.g., ffs)
    \ we use binary search
    cell-bits 1- swap
    cell-bits-shift 0 ?do ( u1 x1 )
	cell-bits 2/ i rshift
	2dup lshift dup if ( u1 x1 shift x2 )
	    >r nip - r>
	else
	    2drop
	endif
    loop
    drop ;

: find-next-bit ( u1 addr -- u2 )
    \ find the first u2>=u1 in bit-vector addr that is set
    \ assumes that there is something to find
    dup >r
    -1 bit-addr-mask tuck @ and begin ( addr1 x1 )
	dup 0=
    while
	drop cell+ dup @
    repeat
    first-bit swap r> - addr-bit ;

: and! ( mask addr -- )
    \ like +! to +
    tuck @ and swap ! ;

: clear-bits ( u1 u2 addr -- )
    \ clear all bits from u1 (incl.) to u2 (excl.) in bit-vector at addr
    assert2( >r 2dup u<= r> swap )
    tuck -1 bit-addr-mask ( u1 addr mask2 addr2 )
    2swap -1 bit-addr-mask swap invert swap ( mask2 addr2 mask1 addr1 )
    rot 2dup = if  ( mask2 mask1 addr1 addr2 )
	 \ both masks are for the same cell
	drop >r or r> and!
    else
	over cell+ 2dup - erase \ clear the memory in between
	>r and! \ deal with the last cell
	r> and! \ deal with the first cell
    endif ;

\ -------------------------------
\ border and liveness information

\ we use one bit per grain to mark the borders of chunks and one for
\ the liveness. For typical 64-bit chunks this results in a 3% space
\ overhead.

\ The bit corresponding to the first grain of a chunk is set in the
\ borders bitset. Similarly, after the mark phase the bit
\ corresponding to the first grain of a chunk is set, if the chunk is
\ alive (approximated by "reachable from the root set"). Using the
\ first grain makes it easy determine whether a (suspected) pointer
\ points to the start of a chunk and whether it points to the start of
\ a chunk already marked as live.

variable border
variable live

1 cells 1 faligned 1 dfaligned max max constant grain

: grains ( u1 -- u2 )
    \ u2=u1*grain
    [ grain log2 ] literal lshift ;

: grain/ ( u1 -- u2 )
    \ u2=u1/grain
    [ grain log2 ] literal rshift ;

: grain-aligned? ( u -- f )
    [ grain 1- ] literal and 0= ;

: grain-addr-num ( addr1 -- u )
    assert2( dup memory-block @ memory-block-end @ grain 2* + within )
    assert2( dup grain-aligned? )
    memory-block @ - grain/ ;

: grain-num-addr ( u -- addr )
    grains memory-block @ + ;

: set-grain ( addr1 bitvector -- )
    swap grain-addr-num swap set-bit ;

: grain-set? ( addr1 bitvector -- f )
    swap grain-addr-num swap bit-set? ;

: allocate-grain-info ( addr1 -- addr2 )
    \ allocate a bitvector (addr2) for the grains until addr1 (+2 bits)
    grain-addr-num 2 + bit-addr nip cell+ ( size )
    dup allocate throw ( size addr2 )
    dup rot erase ;

\ -----------
\ linked list

struct
    cell% field list-next
end-struct list%

: delete-node ( list-addr -- )
    \ delete node at the start of the list
    dup @ list-next @ swap ! ;

: insert-node ( node list-addr -- )
    tuck @ over list-next ! ( list-addr node )
    swap ! ;

\ ---------------
\ root management

list%
    cell% field rootlist-addr \ address of a root
end-struct rootlist%

variable other-roots 
0 other-roots !

\ ---------
\ mark pass

: mark? ( x -- f )
    \ can x be a pointer to an unmarked gc chunk?
    dup [ grain 1- ] literal and 0= if \ if x is chunk-aligned
	dup memory-block @ active-end @ within if \ and x points into gc memory
	    dup border @ grain-set? if \ and x points to the start of a chunk
		live @ grain-set? 0= EXIT
	    endif
	endif
    endif
    drop false ;

over [IF]
\ recursive mark, fast and simple, but needs deep stacks

\ I want to avoid having a DO LOOP in mark at run-time (for time and
\ space reasons), so I unroll it at compile-time using gen-mark.  "see
\ mark" to see what is actualy generated.
: gen-mark ( -- ; generated code: addr1 -- addr2 )
    \ generates the recursive calls for mark
    \ addr2=addr1+grain
    grain 0 ?do
	POSTPONE dup POSTPONE @ POSTPONE recurse POSTPONE cell+
	1 cells +loop ;

: mark ( x -- )
    \ if x is a pointer to a gc chunk, mark it and its descendents
    assert2( active-end @ border @ grain-set? )
    dup mark? if
	dup live @ set-grain
	begin ( x1 )
	    [ gen-mark ]
	    dup border @ grain-set? until
    endif
    drop ;

[ELSE]
\ pointer reversing mark, slow and complex, but gentle to the stacks
\ if the mark phase is interrupted, the data will be corrupt

: chunk-last-cell ( addr1 -- addr2 )
    \ addr1 ist the address of a chunk, addr2 is the address of its last cell
    grain-addr-num 1+ border @ find-next-bit grain-num-addr cell- ;

: start-of-chunk? ( addr -- f )
    assert2( dup dup aligned = )
    [ grain 1 cells <> ] [if]
	dup [ grain 1- ] literal and if
	    drop false EXIT
	endif
    [then]
    border @ grain-set? ;

: mark1 ( x xr u -- )
    \ x is the (address of the) chunk under consideration.
    \ u is the number of reversed pointers (corresponding to the depth
    \ of the "stack"). xr is the pointer to the cell that originally
    \ pointed to x (now this cell contains a reverse pointer).
    >r >r
    dup live @ set-grain \ mark chunk as live
    chunk-last-cell begin ( addr R: u xr )
	dup @ dup mark? if ( addr new-addr ) \ new-addr points to a chunk
	    \ now mark this chunk and its descendents
	    swap r> over ! \ store reverse pointer at addr
	    r> 1+ >r >r ( new-addr R: u+1 addr )
	    dup live @ set-grain \ mark chunk as live
	    chunk-last-cell
	else
	    drop begin ( addr R: u xr )
		dup start-of-chunk?
	    while
		r> r> dup 0= if \ we are done with the first chunk
		    2drop drop EXIT
		endif
		1- >r ( addr xr R: u )
		dup @ >r \ get previous reverse pointer
		tuck !
	    repeat
	    cell-
	endif
    again ;

: mark ( x -- )
    \ if x is a pointer to a gc chunk, mark it and its descendents
    assert2( active-end @ border @ grain-set? )
    dup mark? if
	0 0 mark1
    else
	drop
    endif ;

[THEN]

: mark-stack ( -- )
    depth 0 ?do
	i pick mark
    loop ;

: mark-others ( -- )
    other-roots @ begin
	dup
    while
	dup rootlist-addr @ @ mark
	list-next @
    repeat
    drop ;

: mark-all ( -- )
    mark-stack mark-others ;

\ -------------------
\ freelist management

\ GC has one freelist for each chunk size; the freelists are kept in a
\ linked list, sorted by chunk size (starting with the smallest). If
\ most allocated and collected chunks are small, the performance
\ should be ok; otherwise it would be better to use a more efficient
\ representation (e.g., a tree).

\ we manage the lists of freelists with ALLOCATE and FREE, because we
\ cannot allocate from GCed memory during the sweep phase.

list%
    cell% field freelist-size \ chunk size
    cell% field freelist-list \ linked list of chunks
end-struct freelist%

\ the last freelist has an impossibly large chunk size and serves as
\ sentinel to avoid a test for end-of-list in each iteration of
\ freelist-search
freelist% %allot constant freelist-sentinel
variable freelists 

assert-level @ 1 > [if]
\ freelist consistency
: check-freelist ( addr usize -- )
    \ check that all list elements are chunks of size usize
    assert( dup 0<> ) \ every list except the sentinel has at least one element
    grain/ >r begin
	dup
    while
	assert2( dup border @ grain-set? )
	assert2( dup grain-addr-num dup 1+ border @ find-next-bit swap - r@ = )
	@
    repeat
    r> 2drop ;

: check-freelists ( -- )
    freelists @ begin
	dup freelist-sentinel <>
    while
	dup freelist-list @ over freelist-size @ check-freelist
	list-next @
    repeat
    drop ;
[then]

: freelist-search ( u freelist-addr1 -- freelist-addr2 freelist )
    \ search for the first freelist with chunk size >= u.
    \ freelist-addr are addresses of cells containing pointers to
    \ freelist% nodes.  The additional indirection allows inserting or
    \ removing nodes.  freelist is "freelist-addr2 @".
    swap assert2( dup -1 u< ) >r begin ( freelist-addr )
	dup @
	dup freelist-size @ r@ u<
    while ( freelist-addr freelist )
	nip list-next
    repeat
    r> drop ;

: take-free-chunk ( freelist-addr freelist -- addr )
    \ take first chunk from freelist; if freelist becomes empty,
    \ remove the whole freelist node
    dup freelist-list @ assert2( dup ) ( freelist-addr freelist chunk )
    dup list-next @ dup if \ there is another chunk
	( freelist-addr freelist chunk next-chunk )
	rot freelist-list !
	nip
    else \ freelist empty, remove it
	drop rot delete-node ( freelist chunk )
	swap free throw
    endif ;

: insert-free-chunk ( addr u -- )
    over border @ set-grain
    dup >r freelists freelist-search ( addr freelist-addr freelist )
    dup freelist-size @ r@ u> if \ there is no freelist for this size yet
	drop freelist% %alloc 2dup swap insert-node
	r@ over freelist-size !
	0 over freelist-list !
    endif
    r> drop nip ( addr freelist )
    freelist-list insert-node ;

: clear-freelist ( freelist -- )
    \ clear one freelist; this is done to avoid having half of a
    \ freelist scooped up by a spurious pointer into it
    assert( dup 0<> )
    begin
	dup @
	0 rot !
	dup 0= until
    drop ;

: free-freelists ( freelists -- )
    begin ( freelist )
	dup freelist-sentinel <>
    while
	dup freelist-list @ clear-freelist
	dup list-next @
	swap free throw
    repeat
    drop ;

\ --------------------------------
\ policy for setting current-limit

variable current-limit	   \ when active-end reaches current-limit, collect!
2variable size-factor
variable size-offset 
variable live-grains
\ live-grains may be too large by one (if the last chunk is live), but
\ that's no problem as it is only used for a heuristic calculation.

: set-current-limit ( -- )
    live-grains @ size-factor 2@ */ size-offset @ + grain-num-addr ( addr )
    active-end @ over a> if
	drop active-end @
    endif
    dup memory-block-end @ a> if
	drop memory-block-end @
    endif
    current-limit ! ;

\ ----------
\ sweep pass

: sweep-live ( u1 -- u2 )
    \ starting at u1 (the start of a live chunk), search for the next
    \ dead chunk, which starts at u2
    \ no need to check for active-end, since we will hit the sentinel anyway
    \ this can be accelerated by doing a simple find-next-bit on border&~live
    assert2( dup live @ bit-set? over border @ bit-set? and )
    begin ( u )
	1+ border @ find-next-bit 
	dup live @ bit-set? 0= until
;

: one-chunk ( ustart uend -- )
    \ clear all border bits but the first
    \ clearing border bits is not necessary until we allocate the
    \ chunk, but we do it earlier, during the sweep pass, to prevent
    \ spurious hits on the next garbage collection (OTOH, if there is
    \ a spurious hit, the spuriously live chunk is larger).
    assert2( over border @ bit-set? )
    assert2( dup  border @ bit-set? )
    swap 1+ swap border @ clear-bits ;

: erase-chunk ( ustart uend -- )
    \ erasing the chunk is not necessary, but useful for two reasons:
    \ 1) it destroys pointers to other chunks that would keep those
    \ chunks alive if the present chunk becomes spuriously alive (or
    \ allocated without initalization).
    \ 2) when done during the sweep pass it makes it easier to notice
    \ bugs that result in freeing live chunks
    over grain-num-addr swap rot - grains erase ;

: free-chunk ( ustart uend -- )
    2dup one-chunk
    2dup erase-chunk
    over - grains ( ustart aus )
    swap grain-num-addr swap insert-free-chunk ;

: sweep1 ( uactivestart uactiveend -- )
    >r dup live @ bit-set? 0= IF ( C: orig ) \ jump into loop (to the THEN)
    begin ( u )
	assert2( dup live @ bit-set? 0= )
	dup 1+ live @ find-next-bit ( ustart uend )
	dup r@ u>= if ( ustart uend )
	    assert2( dup r@ = )
	    2dup one-chunk
	    2dup erase-chunk
	    drop grain-num-addr active-end !
	    r> drop EXIT
	endif
	2dup free-chunk nip
	( C: orig dest ) [ 1 CS-ROLL ] THEN ( ustart2 )
        dup sweep-live ( ustart2 uend2 )
	dup rot - live-grains +!
	dup r@ u>= if ( u )
	    assert2( dup r@ 1+ = )
	    r> 2drop EXIT
	endif
    again ;

: set-sweep-sentinel ( u -- )
    \ set sentinel: a live chunk at active-end
    dup border @ set-bit
    dup live @ set-bit
    1+ border @ set-bit ;

: sweep ( -- )
    active-end @ grain-addr-num ( u )
    dup set-sweep-sentinel
    0 over sweep1
    \ remove sentinel from border; live is dead after sweep, so never
    \ mind that
    dup 2 + border @ clear-bits ;
    
\ ---------------------
\ the allocation proper

s" Out of GC-managed memory" exception constant gc-out-of-memory

: alloc-freelist ( u -- a-addr ior )
    \ allocate u aus from the freelist or give an error
    assert2( dup grain-aligned? )
    dup freelists freelist-search ( u freelist-addr freelist )
    dup freelist-sentinel = if \ found nothing
	2drop drop 0 gc-out-of-memory EXIT
    endif
    dup freelist-size @ >r
    take-free-chunk ( u addr )
    assert2( over r@ u<= )
    over r@ u< if \ the chunk is too large
	2dup over + r@ rot - insert-free-chunk
    endif
    0 over list-next ! \ clear pointer to next free chunk;
                       \ everything else is already clear
    nip r> drop 0 ;

: alloc-end ( u -- a-addr ior )
    \ allocate u aus from between active-end and current-limit
    assert2( dup grain-aligned? )
    active-end @
    dup border @ set-grain
    assert2( over false swap grain ?do
	    over i + border @ grain-set? or grain +loop
	0= )
    2dup + dup current-limit @ a> if ( u active-end sum )
	drop nip gc-out-of-memory
    else
	active-end !
	dup rot erase
	0
    endif ;

: alloc-nocollect ( u -- a-addr ior )
    assert2( dup grain-aligned? )
    assert3( check-freelists true )
    dup alloc-freelist if
	drop alloc-end
    else
	nip 0
    endif ;

: alloc-extend ( u -- a-addr ior )
    \ allocate u aus from behind active-end, extending current-limit
    assert2( dup grain-aligned? )
    memory-block-end @ current-limit !
    alloc-end
    active-end @ current-limit ! ;

\ Initialize all pointers to correct values. (Except other-root which is
\ static within an image.)
: init-gc-pointer ( -- )
  0 memory-block !
  0 memory-block-end !
  0 active-end !
  0 border !
  0 live !
  0 current-limit !
  3 1 size-factor 2! \ a fraction; the default is 3/1
  32 1024 * size-offset ! \ number of grains
  0 live-grains ! \ grains live after last collection
  0  freelist-sentinel list-next !
  -1 freelist-sentinel freelist-size ! \ dependence: two's complement arithmetic
  0  freelist-sentinel freelist-list !
  freelist-sentinel freelists ! \ list of freelists
;

\ Initial memory size.
variable gc-init-mem

\ initialization
: init-gc-mem ( -- )
  init-gc-pointer
  gc-init-mem @
  1- grain 1- invert and grain + \ round up
  dup allocate throw \ size addr
  dup memory-block ! \ size addr
  dup active-end ! \ size addr
  + dup memory-block-end ! \ end
  allocate-grain-info border ! \
  set-current-limit ;

\ -------
\ the API

set-current

\ Does gc talk much?
: gc-verbose ( flag -- ) i/o? ! ;
false gc-verbose

\ Set the default size of gc managed memory. Changes take effect after the
\ load of the image containing gc.fs.
: gc-setmem ( nBytes -- ) gc-init-mem ! ;
1024 1024 * gc-setmem

\ Call init-gc after setting the memory size. If you want to save an image
\ containing gc.fs,  call gc-setmem before saving. You don't need to call
\ init-gc in you init word.
: init-gc init-gc-mem ;

: collect-garbage ( -- )
    ?"  GC"
    assert2( check-freelists true )
    0 live-grains !
    freelists @  freelist-sentinel freelists !  free-freelists
    active-end @ allocate-grain-info live !
    active-end @ border @ set-grain \ set end of last chunk
    ?" M" mark-all BS
    ?" S" sweep BS
    live @ free throw
    set-current-limit
    assert2( check-freelists true )
    BS BS BS ;

: alloc ( u -- a-addr ior )
    \ allocate u aus
    grain nalign
    dup alloc-nocollect if ( u addr )
	drop ['] collect-garbage catch
	?dup-if
	    EXIT
	endif
	dup alloc-nocollect if ( u addr )
	    drop alloc-extend EXIT
	endif
    endif
    nip 0 ;

: root-address ( a-addr -- )
    \ tells GC that a-addr may contain a pointer into memory managed by GC
    rootlist% %size allocate throw \ use alloc instead of allocate?
    tuck rootlist-addr !
    other-roots insert-node ;

previous

\ This is how the application could initialize the garbage collector
\ on system start
\  : cold-gc ( -- )
\  [ S" gforth" environment? ] [IF] [ 2drop ]
\    defers 'cold
\  [THEN]
\    gc-init-mem
\  ; 

\  S" gforth" environment? [IF] 2drop
\  ' cold-gc is 'cold
\  [THEN]


\ stack at end:
( f-deep )

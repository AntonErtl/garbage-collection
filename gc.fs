\ initialized garbage collection

\ Copyright (C) 1999 M. Anton Ertl

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
\ u-size f-verbosity f-deep-stacks -- u-size f-verbosity f-deep-stacks

s" gc4image.fs" included

2 pick gc-setmem
over gc-verbose
init-gc

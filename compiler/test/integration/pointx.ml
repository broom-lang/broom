val getX = fn point: {y: Int, x: Int} => point.x
val xr: {x: Int} = {x = 23}
val y = 17
val xy: {x: Int, y: Int} = {y, x = 23}
val x: Int = getX {z = 5 .. xy}


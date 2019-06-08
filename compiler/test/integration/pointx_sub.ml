val getX = fn point: {x: Int, y: Int &} => point.x
val xr: {x: Int} = {x = 23}
val y = 17
val xy: {x: Int, y: Int} = {y .. xr}
val x: Int = getX {z = 42 .. xy}


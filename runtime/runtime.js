"use strict";

var Bounce = function (callee, args) {
    this.callee = callee;
    this.arguments = args;
};

var Land = function (result) {
    this.result = result;
};

var MAX_FRAME_COUNT = 1000;

var MetaContinuation = function () {
    this.frameCount = 0;
};

var safePoint = function (f, metaCont) {
    if (metaCont.frameCount < MAX_FRAME_COUNT) {
        metaCont.frameCount += 1;
        return metaCont;
    } else {
        metaCont.frameCount = 0;
        throw new Bounce(f, Array.prototype.slice.call(arguments))
    }
};

var halt = function (_self, _mk, result) {
    throw new Land(result);
};

var run = function (f/*, ...args */) {
    var metaCont = new MetaContinuation();
    var args = Array.prototype.slice.call(arguments, 1);
    var bounce = new Bounce(f, [f, metaCont, halt].concat(args));
    for (; /* ever */;) {
        try {
            bounce.callee.apply(this, bounce.arguments);
        } catch (err) {
            if (err instanceof Bounce) {
                bounce = err;
            } else if (err instanceof Land) {
                return err.result;
            } else {
                throw err;
            }
        }
    }  
};

var wean = function (f) {
    return function () {
        var args = Array.prototype.slice.call(arguments);
        return run.apply(this, [f].concat(args));
    };
};

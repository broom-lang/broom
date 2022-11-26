let to_cfg ~debug program =
    let open PPrint in

    let program = CpsConvert.convert (Fc.Type.Prim Int) program in
    if debug then begin
        Util.debug_heading "CPS from CPS-conversion";
        Util.pprint (Cps.Program.to_doc program ^^ twice hardline)
    end;

    let program = Untuple.untuple program in
    if debug then begin
        Util.debug_heading "CPS after untupling";
        Util.pprint (Cps.Program.to_doc program ^^ twice hardline);
    end;

    let program = ScheduleData.schedule program in
    if debug then begin
        Util.debug_heading "CFG from Dataflow Scheduling";
        Util.pprint (Cfg.Program.to_doc program ^^ twice hardline)
    end;

    program


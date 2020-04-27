let doc_to_string doc =
    let buf = Buffer.create 0 in
    PPrint.ToBuffer.compact buf doc;
    Buffer.contents buf


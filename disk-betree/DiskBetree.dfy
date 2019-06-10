abstract module DiskBetree {
  import BC : BlockCache

  datatype BufferEntry = Insertion(key: Key, value: Value);

  datatype Buffer = Buffer(imap<Key, seq<BufferEntry>>);
  datatype Slot = Slot(child: BC.Reference, buffer: Buffer);
  datatype Node = Node(slots: imap<Key, Slot>);

  datatype Constants = Constants(bcc: BC.Constants);
  datatype Variables = Variables(bcv: BC.Variables);
}

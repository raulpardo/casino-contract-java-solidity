import logger.Logger;

import blockchain.Message;
import blockchain.Block;
import blockchain.Transaction;
import blockchain.types.Uint256Int;
import blockchain.types.Address;
import casino.contract.Casino;

class Main {
  public static void main(String[] args) {

    // Create a few testing addresses
    byte[] address_id_0 = "contract_1".getBytes();
    byte[] address_id_1 = "contract_2".getBytes();
    byte[] address_id_2 = "contract_3".getBytes();
    Address add0 = new Address(address_id_0);
    Address add1 = new Address(address_id_1);
    Address add2 = new Address(address_id_2);

    add0.balance = new Uint256Int(120); // Give 120 wei to add0

    // Build a Transaction
    Transaction tx = new Transaction(
                      new Uint256Int(50),// 50 units of wei per transaction
                      add1);             // the originator of the transaction
                                         // is the contract at add1

    // Build a block
    Block bl = new Block();
    bl.coinbase = add2; // add2 set as the miner
    bl.difficulty = new Uint256Int(1); // set a difficulty of 1?
    bl.gaslimit = new Uint256Int(100); // limit to 100 units of gas
    bl.number = new Uint256Int(1); // block number 1
    bl.timestamp = new Uint256Int(1); // timestamp 1 as well

    // Build a message
    Message msg = new Message();
    msg.sender = add0; // from add0
    msg.gas = new Uint256Int(23); // with 23 units of gas
    msg.data = new byte[] {0,1,2,3,4,5,6,7,8,9}; // a random payload
    msg.value = new Uint256Int(25); // with 25 units of wei

    // Create an logger
    Logger l = new Logger();

    // Add the previous addresses to the logger
    l.addAddress(add0);
    l.addAddress(add1);
    l.addAddress(add2);


    System.out.println(l.currentBalanceOfAddresses());

    Casino c = new Casino(address_id_1,
                          l,
                          msg, bl, tx);

    try {
      //TODO(raul): Check the exception throwing. It needs to be also printed in
      //the in inner classes
      // For simplicity I re-use the same `msg`, `bl` and `tx`, but it should be a new message.
      c.call_addToPot(new Uint256Int(25), msg, bl, tx);
    } catch (Exception e) {
      System.out.println("An exception has occurred: " +  e);
    }

    l.printTrace();
    System.out.println(l.currentBalanceOfAddresses());
  }
}

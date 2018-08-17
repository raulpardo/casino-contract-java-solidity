package logger;

import java.util.ArrayList;

import blockchain.types.Address;

public class Logger {

  // For now, a trace is a sequence of String where each string represents the
  // state fo the contracts.
    private ArrayList/*<String>*/ trace;
    private ArrayList/*<Address>*/ addresses; // List of addresses to monitor

  public Logger() {
      trace = new ArrayList/*<String>*/();
      addresses = new ArrayList/*<Address>*/();
  }

  public void add(String s) {
    trace.add(s);
  }

  public void addAddress(Address a) {
    addresses.add(a);
  }

  // TODO(raul) this method is public only for testing purposes
  public String currentBalanceOfAddresses() {
    String balances = "Balances: [";
    for (Object o : addresses) {
      Address a = (Address) o;  // to avoid generics with KeY
      balances += "(" + new String(a.address) + ", " + a.balance + "), ";
    }
    balances += "]";

    return balances;
  }

  public void printTrace() {
    System.out.println(this.trace);
  }
}

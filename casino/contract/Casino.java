package casino.contract;

import logger.Logger;
import blockchain.Block;
import blockchain.Message;
import blockchain.Transaction;
import blockchain.types.Address;
import blockchain.types.Uint256;
import blockchain.types.Uint256Int;
import javacard.framework.JCSystem;

public final class Casino extends Address {

        private static final Exception REQUIRES_FAILED = new Exception();

        // == INVARIANTS ==

        // ** Gordon syntax **
        // INVARIANT (which is not included in the individual functions):
        //    { state' == State.BET_PLACED ==> pot + wager.value == this.balance &&
        //      !(state' == State.BET_PLACED) ==> pot == this.balance
        //    }

        // ** JML Syntax **
        //@ ghost boolean abortCase;

    
         /*@ public invariant (\forall Address o; \dl_intersect(o.footprint, \set_union(\singleton(this.abortCase),\singleton(javacard.framework.JCSystem._transactionDepth))) == \empty) &&
           @   (\forall Block o; \dl_intersect(o.footprint, \set_union(\singleton(this.abortCase),\singleton(javacard.framework.JCSystem._transactionDepth))) == \empty) &&
           @   (\forall Message o; \dl_intersect(o.footprint, \set_union(\singleton(this.abortCase),\singleton(javacard.framework.JCSystem._transactionDepth))) == \empty) &&
           @   (\forall Transaction o; \dl_intersect(o.footprint, \set_union(\singleton(this.abortCase),\singleton(javacard.framework.JCSystem._transactionDepth))) == \empty); 
           @*/
          /*@ public invariant (\forall Address o; \dl_intersect(o.footprint, \all_objects(<transactionConditionallyUpdated>)) == \empty) &&
            @   (\forall Block o; \dl_intersect(o.footprint,\all_objects(<transactionConditionallyUpdated>)) == \empty) &&
            @   (\forall Message o; \dl_intersect(o.footprint, \all_objects(<transactionConditionallyUpdated>)) == \empty) &&
            @   (\forall Transaction o; \dl_intersect(o.footprint, \all_objects(<transactionConditionallyUpdated>)) == \empty); 
            @*/

        // Datatype to model coin flips
        public static class Coin { public static final int HEADS = 0, TAILS = 1;};

        // State of the contract
        public static class State { public static final int IDLE = 0, GAME_AVAILABLE = 1, BET_PLACED = 2; }

        /*@ public invariant (state == State.BET_PLACED ? pot.sum(wager.value).eq(this.balance) : pot.eq(this.balance)) &&
          @                   (state == State.IDLE || state == State.GAME_AVAILABLE || state == State.BET_PLACED);   
          @*/
        private /*@ spec_public @*/ int /* State */ state;

        
        // Variables
        //@ public invariant \invariant_for(operator) && operator != this && !this.eq(operator);
        public/*@ spec_public @*/ Address operator;     // originally address (20 bytes address)

        //@ public invariant \invariant_for(pot);
        public /*@ spec_public @*/ Uint256 pot;          // originally uint256 (256 bits unsigned integer). Using `long` we loose precision (it is only a 64 bit integer)

        //@ public invariant \invariant_for(timeout);
        public /*@ spec_public @*/ Uint256 timeout;      // originally uint (uint is an alias for uint256)
        //@ public invariant \invariant_for(secretNumber);
        public /*@ spec_public @*/  Uint256 secretNumber; // originally bytes32 (32 bytes array, array with 32 positions each a byte of memory)
        // We use Uint256 for simplicity since we will
        // not verify anything specific to the byte
        // array. TODO: Discuss with others.
        //@ public invariant \invariant_for(player) && !player.eq(this) && this != player;
        public /*@ spec_public @*/ Address player;       // originally address

        final class Wager {
                /*@ public invariant \invariant_for(value); @*/
                public Uint256 value;
                /*@ public invariant guess == Coin.HEADS || guess == Coin.TAILS; @*/
                public int /* Coin */ guess;
                /*@ public invariant \invariant_for(timestamp); @*/
                public Uint256 timestamp;
        }
        //@ public invariant \invariant_for(wager);
        private /*@ spec_public @*/ Wager wager;

        // Magical global variables to access the blockchain
        //@ public invariant \invariant_for(msg) && !msg.sender.eq(this);
        /*@ spec_public @*/ Message msg;      // This can change in any *external* function call
        //@ public invariant \invariant_for(block) && !block.coinbase.eq(this);
        /*@ spec_public @*/ Block block;      // Remain the same in the same block
        //@ public invariant \invariant_for(tx) && !tx.origin.eq(this);
        /*@ spec_public @*/ Transaction tx;   // Remain the same in the same transaction

        // Extra variable to model contract selfdestruct
        /*@ spec_public @*/ boolean destroyed;

        // Logger
        /*@ spec_public @*/ Logger logger;

        // Constants
        /*@ spec_public @*/final int DEFAULT_TIMEOUT = 30;
        //@ private represents footprint = \set_minus(this.*, \set_union(\singleton(this.abortCase), \singleton(javacard.framework.JCSystem._transactionDepth))), this.address[*], operator.footprint, this.player.footprint, wager.*, msg.footprint, block.footprint, tx.footprint;


        // Requires
        /*@ public normal_behavior
          @ requires b;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires !b;
          @ signals_only Exception;
          @ signals (Exception) true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @*/
        private /*@ helper @*/ void require(boolean b) throws Exception {
                if (!b) {
                        //abortTr // We abort the current transaction if an exception is thrown
                        throw REQUIRES_FAILED;//RequireViolationException();
                }
        }

        // Assert -- NOT USED so far
        // private void assert(boolean b) {
        //   if (!b) {
        //     //abortTr // We abort the current transaction if an exception is thrown
        //     throw new AssertViolationException();
        //   }
        // }

        // Create a new casino

        // ** Gordon syntax **
        // PRE: { operator == null }
        // POST: { operator != null }

        // ** JML syntax **
        /* public normal_behaviour
          @ requires operator == null;
          @ ensures operator != null;
          @*/
        public Casino(byte[] contract_address, // Address _operator,
                                                                Logger _logger,
                                                                Message _msg, Block _block, Transaction _tx) {
                super(contract_address);
                // byte[] a = {0,1,2,3,4,5,6,7,8,9};
                // Global magic variables are parameters of the constructor
                // TODO: Discuss with others if this is ok for modelling messages to the contract
                // this.msg = _msg;
                // this.block = _block;
                // this.tx = _tx;

                // Initialization as in the original contract
                operator = _msg.sender;
                state = State.IDLE;
                timeout = new Uint256Int(DEFAULT_TIMEOUT);
                pot = Uint256.ZERO;
                wager = new Wager();
                wager.value = Uint256.ZERO;

                // Initially the contract is not destroyed
                // TODO(raul): Check in all calls that the contract is not destroyed
                destroyed = false;

                //Initialisation of the logger
                logger = _logger;
        }

        // Modifiers (except for payable, which is defined in Address)
        /*@ public normal_behavior
          @ requires msg.value.eq(_value);
          @ ensures true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires !msg.value.eq(_value);
          @ signals_only Exception;
          @ signals (Exception) true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @*/
        public void costs(Uint256 _value) throws Exception {
                // We just unfold the require
                this.require(msg.value.eq(_value));
        }

        /*@ public normal_behavior
          @ requires<heap> msg.sender.eq(operator);
          @ ensures<heap> true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires !msg.sender.eq(operator);
          @ signals_only Exception;
          @ signals (Exception) true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @*/
         public void byOperator() throws Exception {
                // We just unfold the require
                this.require(msg.sender.eq(operator));
        }

        /*@ public normal_behavior
          @ requires state == State.IDLE || state == State.GAME_AVAILABLE;
          @ ensures true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires state != State.IDLE && state != State.GAME_AVAILABLE;
          @ signals_only Exception;
          @ signals(Exception) true;
          @ assignable<heap><savedHeap> \strictly_nothing;
          @
          @*/
          public /*@ helper @*/ void noActiveBet() throws Exception {
                this.require(state == State.IDLE || state == State.GAME_AVAILABLE);
         }

         /*@ public normal_behavior
           @ requires _state == state;
           @ ensures true;
           @ assignable<heap><savedHeap> \strictly_nothing;
           @
           @ also
           @
           @ public exceptional_behavior
           @ requires<heap><savedHeap> _state != state;
           @ signals_only Exception;
           @ signals (Exception) true;
           @ assignable<heap><savedHeap> \strictly_nothing;
           @
           @*/
         public /*@ helper @*/ void inState(int _state) throws Exception {
                this.require(_state == state);
        }

        // Auxiliary function to update magical variables
            /*@ public normal_behavior
          @ requires \invariant_for(_msg) && !_msg.sender.eq(this);
          @ requires \invariant_for(_block) && !_block.coinbase.eq(this);
          @ requires \invariant_for(_tx) && !_tx.origin.eq(this);
          @ ensures msg == _msg && block == _block && tx == _tx;
          @ assignable msg, block, tx;
          @ assignable<savedHeap> \strictly_nothing;
          @*/
        public void updateBlockchainVariables(Message _msg, Block _block, Transaction _tx) {
                msg = _msg;
                block = _block;
                tx = _tx;
        }

        // Functions

        public void call_updateTimeout(Uint256 _timeout, Message _msg, Block _block, Transaction _tx) {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        // The transaction starts after updating the variables because those will
                        // not be reverted.
                        JCSystem.beginTransaction();
                        this.updateTimeout(_timeout);
                        // If everything goes fine, then we commit the transaction
                        JCSystem.commitTransaction();
                } catch(Exception e) {
                        // 1. Restore control flow and
                        // 2. Abort the transaction
                        //abortTrJCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        System.out.println(e);
                }
        }

        // ** Gordon Syntax **
        // PRE: {}
        // POST: { operator' == operator && state == state' && pot' == pot && wager' == wager }

        // ** JML syntax **
      /*@ public normal_behavior
        @ requires msg.sender.eq(operator);
        @ requires state == State.IDLE || state == State.GAME_AVAILABLE;
        @ requires \invariant_for(_timeout);
        @ ensures this.timeout == _timeout;
        @ assignable this.timeout; // Probably the assignable clause is enough.
        @ assignable<savedHeap> \strictly_nothing;
        @
        @ also
        @
        @ public exceptional_behavior
        @ requires ((state != State.IDLE && state != State.GAME_AVAILABLE) ||
        @           !msg.sender.eq(operator));
        @ signals (Exception) true;
        @ assignable \nothing;
        @ assignable<savedHeap> \strictly_nothing;
        @*/
        public void updateTimeout(Uint256 _timeout) throws Exception {
                // Modifiers
                this.byOperator();
                this.noActiveBet();

                // Body
                this.timeout = _timeout;
        }


        public void call_addToPot(Uint256 value, Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.addToPot(value);
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
                logger.add("addToPot");
        }

        // ** Gordon syntax **
        // PRE: {}
        // POST: { operator' == operator && state == state' && wager' == wager && timeout' == timeout &&
        //          (operator == msg.owner &&  msg.value > pot) ==> pot' = pot + msg.value &&
        //          !(operator == msg.owner &&  msg.value > pot) ==> pot' == pot'
        // }

  // comment(raul): Here could add to the invariant that this.balance is also
  // increased (by msg.value) in order to verify that the amount of money was
  // actually sent is transfered to the casino's balance.

        // ** JML syntax **
        /*@ public normal_behaviour
          @ requires msg.value.leq(this.balance);
          @ requires operator.eq(msg.sender);
          @ requires value.gr(Uint256.ZERO) && value.eq(msg.value);
          @ requires \invariant_for(value);
          @ ensures pot.eq(\old(pot.sum(value)));
          @ assignable pot;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires !(msg.value.leq(this.balance) && operator.eq(msg.sender) && value.gr(Uint256.ZERO) && value.eq(msg.value));
          @ signals (Exception) true;
          @ assignable \nothing;
          @*/
        public void addToPot(Uint256 value) throws Exception {

                // Modifiers
                this.payable(msg);
                this.byOperator();
                this.costs(value);


                // Require
                this.require(value.gr(Uint256.ZERO));

                this.pot = this.pot.sum(value); // Using Uint256 method
                // TODO; ask Raoul: no transfer?
                //// ANSWER: Not needed, since the payable modifier already includes the //// amount.
        }

        /*@ public normal_behavior
          @ requires JCSystem.getTransactionDepth() == 0;
	  @ requires \invariant_for(value);
          @ requires \invariant_for(_msg) && !_msg.sender.eq(this);
          @ requires \invariant_for(_block) && !_block.coinbase.eq(this);
          @ requires \invariant_for(_tx) && !_tx.origin.eq(this);
          @ requires value.gr(Uint256.ZERO) && value.leq(pot);
          @ requires state == State.IDLE || state == State.GAME_AVAILABLE;
          @ requires _msg.sender.eq(operator);
          @ assignable  pot, msg.sender.balance, this.balance, msg, tx, block, abortCase, \all_objects(<transactionConditionallyUpdated>);
          @ ensures !abortCase ==> pot.eq(\old(pot.sub(value))) &&
          @                        msg.sender.balance.eq(\old(msg.sender.balance.sum(value))) &&
          @                        this.balance.eq(\old(this.balance.sub(value)));
          @ ensures  abortCase ==> (\old(balance) == balance && 
          @                        \old(pot) == pot && 
          @                        \old(msg.sender.balance) == msg.sender.balance);        
          @*/
        public void call_removeFromPot(Uint256 value, Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.removeFromPot(value);
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        // ** Gordon Syntax **
        // PRE: {}
        // POST: { operator' == operator && state == state' && wager' == wager && timeout' == timeout &&
        //          (operator == msg.owner &&  0 < value <= pot) ==> pot' == pot - msg.value &&
        //          !(operator == msg.owner &&  0 < value <= pot) ==> pot' == pot'
        // }

        // ** JML syntax **
        /*@ public behaviour
          @ requires operator.eq(msg.sender);
          @ requires \invariant_for(value);
          @ requires value.gr(Uint256.ZERO) && value.leq(pot);
          @ requires state == State.IDLE || state == State.GAME_AVAILABLE;
          @ assignable pot, msg.sender.balance, this.balance;
          @ assignable<savedHeap> \strictly_nothing;
          @ ensures pot.eq(\old(pot.sub(value)));
          @ ensures msg.sender.balance.eq(\old(msg.sender.balance.sum(value)));
          @ ensures this.balance.eq(\old(this.balance.sub(value)));
	  @ signals_only Exception;
          @ signals (Exception e) true; 
          @ 
          @ also
          @
          @ public exceptional_behaviour
          @ requires \invariant_for(value);
          @ requires !(operator.eq(msg.sender) &&
          @             value.gr(Uint256.ZERO)  && (state == State.IDLE || state == State.GAME_AVAILABLE));
          @ signals (Exception) true;
          @ assignable \strictly_nothing;
          @ assignable<savedHeap> \strictly_nothing;
          @*/
        private void removeFromPot(Uint256 value) throws Exception {
                // Modifiers
                this.payable(msg);
                this.byOperator();
                this.noActiveBet();

                // Requires
                this.require(value.gr(Uint256.ZERO) && value.leq(pot));

                this.pot = this.pot.sub(value); // Using Uint256 method
                msg.sender.transfer(this, value); // strange ask, comment(raul): Fixed.
        }


        public void call_createGame(Uint256 _secretNumber, Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.createGame(_secretNumber);
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        // ** Gordon syntax **
        // PRE: {}
        // POST: { operator' == operator && wager' == wager && timeout' == timeout && pot == pot' &&
        //         (operator == msg.owner) ==>  state == state' &&
        //         !(operator == msg.owner) ==>  state' == State.GAME_AVAILABLE
        // }

        // ** JML Syntax **
        /*@ public normal_behaviour
          @ requires \invariant_for(_secretNumber);
          @ requires operator.eq(msg.sender);
          @ requires state == State.IDLE;
          @ ensures secretNumber == _secretNumber;
          @ ensures state == State.GAME_AVAILABLE;
          @ assignable secretNumber, state;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires !operator.eq(msg.sender) || state != State.IDLE;
          @ signals_only Exception;
          @ signals (Exception) true;
          @ assignable \strictly_nothing;
          @*/
        public void createGame(Uint256 _secretNumber) throws Exception {
                this.byOperator();
                this.inState(State.IDLE);

                secretNumber = _secretNumber;
                state = State.GAME_AVAILABLE;
        }


        public void call_placeBet(Uint256 _value, /* Coin */ int _guess, Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.placeBet(_value, _guess);
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        // ** Gordon syntax **
        // PRE: {}
        // POST: { operator' == operator && timeout' == timeout && pot == pot' &&
        //          (msg.sender != operator && 0 < msg.value <= pot) ==>  wager.value == msg.value && state' == State.BET_PLACED &&
        //          !(msg.sender != operator && 0 < msg.value <= pot) ==>  wager' == wager && state' == state
        // }

        // ** JML syntax **
        /*@ public normal_behaviour
          @ requires \invariant_for(_value);
          @ requires msg.value.leq(this.balance);
          @ requires msg.value.eq(_value);
          @ requires state == State.GAME_AVAILABLE;
          @ requires !(msg.sender.eq(operator));
          @ requires _value.gr(Uint256.ZERO)   && _value.leq(pot);
          @ requires _guess == Coin.HEADS || _guess == Coin.TAILS;
          @ ensures state ==  State.BET_PLACED;
          @ ensures player == msg.sender;
          @ ensures wager.value == _value;
          @ ensures this.wager.guess == _guess;
          @ ensures this.wager.timestamp == block.timestamp;
          @ ensures \fresh (wager) && \invariant_for(wager);
          @ assignable wager, state, player;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires \invariant_for(_value);
          @ requires state != State.GAME_AVAILABLE || msg.sender.eq(operator) ||
          @          !_value.gr(Uint256.ZERO)  || _value.gr(pot) ||
          @          msg.value.gr(this.balance) ||
          @          !msg.value.eq(_value);
          @ signals (Exception e) true;
          @ assignable \nothing;
          @*/
        private void placeBet(Uint256 _value, int /* Coin */ _guess) throws Exception {
                // Modifiers
                this.payable(msg);
                this.costs(_value);
                this.inState(State.GAME_AVAILABLE);

                // Requires
                this.require(!(msg.sender.eq(operator)));
                this.require(_value.gr(Uint256.ZERO) && _value.leq(pot));

                state = State.BET_PLACED;
                player = msg.sender;

                this.wager = new Wager();
                this.wager.value = _value;
                this.wager.guess = _guess;
                this.wager.timestamp = block.timestamp; // `now` is an alias for block.timestamp
                // https://solidity.readthedocs.io/en/latest/units-and-global-variables.html#block-and-transaction-properties
        }



    
        public void call_decideBet(Uint256 publicNumber, Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.decideBet(publicNumber);
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        // ** Gordon syntax **
        // PRE: {}
        // POST: { operator' == operator && timeout' == timeout && pot `elem` { pot - wager.value, pot + wager.value }

        // ** JML syntax **
        /*@ public normal_behaviour
          @ requires \invariant_for(publicNumber);
          @ requires msg.sender.eq(operator);
          @ requires state == State.BET_PLACED;
          @ requires secretNumber.eq(publicNumber.keccak256());
          @ requires publicNumber.mod(Uint256.TWO).eq(Uint256.ZERO) <==> wager.guess == Coin.HEADS;
          @ ensures pot.eq(\old(pot.sub(wager.value)));
          @ ensures player.balance.eq(\old(player.balance.sum(wager.value)));
          @ ensures wager.value.eq(Uint256.ZERO);
          @ ensures this.balance == \old(this.balance.sub(wager.value));
          @ ensures state == State.IDLE;
          @ assignable pot, wager.value, this.balance, state;
          @
          @ also
          @
          @ public normal_behaviour
          @ requires \invariant_for(publicNumber);
          @ requires msg.sender.eq(operator);
          @ requires state == State.BET_PLACED;
          @ requires secretNumber.eq(publicNumber.keccak256());
          @ requires !(publicNumber.mod(Uint256.TWO).eq(Uint256.ZERO) <==> wager.guess == Coin.HEADS);
          @ ensures pot.eq(\old(pot.sum(wager.value)));
          @ ensures wager.value.eq(Uint256.ZERO);
          @ ensures state == State.IDLE;
          @ assignable pot, wager.value, state;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires \invariant_for(publicNumber);
          @ requires !msg.sender.eq(operator) || state != State.BET_PLACED ||
          @   !secretNumber.eq(publicNumber.keccak256());
          @ signals (Exception) true;
          @ assignable \nothing;
          @*/
        private void decideBet(Uint256 publicNumber) throws Exception {
                // Modifiers
                this.byOperator();
                this.inState(State.BET_PLACED);

                //Requires
                this.require(secretNumber.eq(publicNumber.keccak256()));

                int secret = publicNumber.mod(Uint256.TWO).eq(Uint256.ZERO) ? Coin.HEADS : Coin.TAILS; // Change mod and ? for Uint256 equivalents

                if (secret == wager.guess) {
                        playerWins();
                } else {
                        operatorWins();
                }

                state = State.IDLE;
        }


        public void call_timeoutBet(Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.timeoutBet();
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        // ** Gordon syntax **
        // PRE: {}
        // POST: { operator' == operator && timeout' == timeout && pot == pot - wager.value
        // }

        // ** JML syntax **
        /*@ public normal_behaviour
          @ requires msg.sender.eq(player);
          @ requires block.timestamp.sub(wager.timestamp).gr(timeout);
          @ requires state == State.BET_PLACED;
          @ ensures pot.eq(\old(pot.sub(wager.value)));
          @ ensures state == State.IDLE;
          @ assignable pot, wager.value, balance;
          @*/
        public void timeoutBet() throws Exception {
                // Modifiers
                this.inState(State.BET_PLACED);

                // Requires
                this.require(msg.sender.eq(player));
                this.require(block.timestamp.sub(wager.timestamp).gr(timeout)); // now == block.timestamp

                // Body
                playerWins();
                state = State.IDLE;
        }


        // Player wins and gets back twice his original wager
        /*@ private normal_behavior
          @ requires wager.value.mul(Uint256.TWO).leq(player.balance);
          @ ensures pot.eq(\old(pot.sub(wager.value)));
          @ ensures player.balance.eq(\old(player.balance.sum(wager.value.mul(Uint256.TWO))));
          @ ensures wager.value.eq(Uint256.ZERO);
          @ ensures this.balance.eq(\old(this.balance.sub(wager.value.mul(Uint256.TWO))));
          @ assignable this.pot, wager.value, this.balance, player.balance;
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires wager.value.mul(Uint256.TWO).gr(player.balance);
          @ signals (Exception) true;
          @ assignable pot;
          @*/
        private void playerWins() throws Exception {
                pot = pot.sub(wager.value);  // is this correct? I assume that change is rolled back when transfer fails?
                player.transfer(this, wager.value.mul(Uint256.TWO));
                wager.value = Uint256.ZERO;
        }


        // Operator wins, transferring the wager to the pot
        /*@ private normal_behavior
          @ ensures pot.eq(\old(pot.sum(wager.value)));
          @ ensures wager.value.eq(Uint256.ZERO);
          @ assignable this.pot, wager.value;
          @*/
        private void operatorWins() throws Exception {
                pot = pot.sum(wager.value);
                wager.value = Uint256.ZERO;
        }
    
        // Operator closes casino
        /*@ public normal_behavior
          @ requires JCSystem.getTransactionDepth() == 0;
          @ requires \invariant_for(_msg) && !_msg.sender.eq(this);
          @ requires \invariant_for(_block) && !_block.coinbase.eq(this);
          @ requires \invariant_for(_tx) && !_tx.origin.eq(this);
          @ requires state == State.IDLE;
          @ requires _msg.sender.eq(operator);
          @ assignable balance, operator.balance, destroyed, msg, tx, block, abortCase, \all_objects(<transactionConditionallyUpdated>);
          @ ensures !abortCase ==> ( operator.balance.eq(\old(operator.balance.sum(this.balance))) && 
	  @                          this.balance.eq(Uint256.ZERO) && destroyed );
          @ ensures  abortCase ==> (\old(balance) == balance && 
          @                        \old(operator.balance) == operator.balance && 
          @                        \old(destroyed) == destroyed);        
          @*/
        public void call_closeCasino(Message _msg, Block _block, Transaction _tx) throws Exception {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);
                try {
                        JCSystem.beginTransaction();
                        this.closeCasino();
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        /*@ public behavior
          @ requires state == State.IDLE;
          @ requires msg.sender.eq(operator);
          @ assignable balance, operator.balance, destroyed;
          @ assignable<savedHeap> \strictly_nothing;
          @ ensures operator.balance.eq(\old(operator.balance.sum(this.balance)));
          @ ensures this.balance.eq(Uint256.ZERO);
          @ ensures destroyed;
          @ signals_only Exception;
          @ signals (Exception e) true; 
          @
          @ also
          @
          @ public exceptional_behavior
          @ requires state != State.IDLE || !msg.sender.eq(operator);
          @ signals_only Exception;
          @ signals (Exception) true;
          @ assignable \strictly_nothing;
          @ assignable<savedHeap> \strictly_nothing;
          @*/
        public void closeCasino() throws Exception {
                // Modifiers
                this.inState(State.IDLE);
                this.byOperator();

                // Body
                selfdestruct(operator);
        }

        /*@ public normal_behavior
          @ requires \invariant_for(a) && a != this;
          @ ensures a.balance.eq(\old(a.balance.sum(balance)));
          @ ensures this.balance.eq(Uint256.ZERO);
          @ ensures destroyed;
          @ assignable this.balance, a.balance, destroyed;
          @ assignable<savedHeap> \strictly_nothing;
          @*/
        public void selfdestruct(Address a) throws Exception {
                // TODO(raul): Think how to implement all this using `transfer` or `send`

                // Increase the balance of `a`
                a.balance = a.balance.sum(this.balance);

                // Decrease to 0 all the balance of `this`
                this.balance = this.balance.sub(this.balance);

                // Set the contract as destroyed
                this.destroyed = true;
        }


        // Fallback function. TODO: At compile time (translation time), forward calls to undefined methods to fallback. [ALREADY DISCUSSED]
        public void call_fallback(Message _msg, Block _block, Transaction _tx) {
                //@ set abortCase = false;
                this.updateBlockchainVariables(_msg,_block,_tx);

                try {
                        JCSystem.beginTransaction();
                        this.fallback();
                        JCSystem.commitTransaction();
                } catch (Exception e) {
                        JCSystem.abortTransaction();
                        //@ set abortCase = true;
                        ;
                        //System.out.println(e);
                }
        }

        // ** Gordon syntax **
        // PRE: {}
        // POST: { operator' == operator && state == state' && wager' == wager && timeout' == timeout && pot' == pot }

        // ** JML syntax **
        /*@ public normal_behaviour
          @ requires true;
          @ ensures true;
          @ assignable \strictly_nothing;
          @*/
        public void fallback() {
                // Empty body
        }
}

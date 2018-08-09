pragma solidity ^0.4.11;

/// @title Unsafe casino implementation.

// NOTE:
// I am assuming that the preconditions are checked *before* and *after* the modifiers.
// Also, when the modifiers (or require statements inlined) perform certain checks e.g.
// msg.sender == operator, we consider that the function will also work for when the sender
// is not the operator, but will just revert immediately. Also, I've added the fallback
// function to give it a pre/post condition pair.
// I am writing v and v' to refer to the initial value of v, and its final value (so in
// KeY v would correspond to old(v), I believe).
//
// INVARIANT (which is not included in the individual functions):
//    { state' == State.BET_PLACED ==> pot + wager.value == this.balance &&
//      !(state' == State.BET_PLACED) ==> pot == this.balance
//    }

contract Casino {
	//
	// A coin-tossing casino contract working as follows:
	//  * An operator may create a contract with an empty pot and timeout of 30min
	//  * The operator may add money to the pot at any time
	//  * As long as no player has placed a bet, the operator may (i) withdraw money
	//    from the pot and change the timeout value; (iii) submit a hashed secret number
	//    (even if she chooses HEADS, odd if she chooses TAILS)
	//  * A (non-operator) player may then place a bet (up to the size of the pot) with
	//    a guess of HEADS or TAILS
	//  * The operator may then submit her original number to resolve the bet
	//  * If the operator has not submitted her number by the timeout (from when the
	//   player placed the bet), the player may ask for a default win
	//  * If the player has won, he gets to withdraw his wager+that value from the pot
	//  * If the casino has won, the wager goes to the pot
	//
	// EXPECTED BEHAVIOUR: The operator may not reduce the pot while a bet is active.
	//


	// Identity of who is running the casino
	address public operator;

	// The player is allowed to register a win if the operator does not
	// resolve a wager within this timeout
	uint public timeout;
	uint constant DEFAULT_TIMEOUT = 30 minutes;

	// The current pot of money which the operator is making available
	uint256 public pot;

	// The secret number submitted by the operator
	bytes32 public secretNumber;

	// Identity of the player (if any)
	address public player;

	// The current wager (if any)
	enum Coin { HEADS, TAILS }
	struct Wager {
		uint256 value;
		Coin guess;
		uint timestamp;
	}
	Wager private wager;

	// The state of the contract
	enum State { IDLE, GAME_AVAILABLE, BET_PLACED }
	State private state;

	// -----------------------------------------
	// Modifiers
	//
	// Modifier to check cost matches message value
	modifier costs(uint256 _value) {
        require (msg.value == _value);
        _;
    }

	// Modifier to check state
    modifier inState(State _state) {
    	require (_state == state);
    	_;
    }

    // Modifier to check that the message was initiated by the operator
    modifier byOperator() {
    	require (msg.sender == operator);
    	_;
    }

    // Modifier to check that no bet is currently in place
    modifier noActiveBet() {
    	require (state == State.IDLE || state == State.GAME_AVAILABLE);
    	_;
    }
	// -----------------------------------------


	// Create a new casino
	function Casino() public {
    // PRE: { operator == null }

		operator = msg.sender;
		state = State.IDLE;
		timeout = DEFAULT_TIMEOUT;
		pot = 0;
		wager.value = 0;

    // POST: { operator != null }
	}

	// Changing the timeout value
	function updateTimeout(uint _timeout) public
		byOperator
		noActiveBet
	{
    // PRE: {}

		timeout = _timeout;

    // POST: { operator' == operator && state == state' && pot' == pot && wager' == wager && timeout' == _timeout }
	}

	// Add money to pot
	function addToPot(uint256 value) public
		payable
		byOperator
		costs(value)
	{
    // PRE: {}

		// The operator can choose a positive value to pay and raise the pot by
		require (value > 0);


		pot = pot + value;

    // POST: { operator' == operator && state == state' && wager' == wager && timeout' == timeout &&
    //          (operator == msg.owner &&  msg.value > pot) ==> pot' = pot + msg.value &&
    //          !(operator == msg.owner &&  msg.value > pot) ==> pot' == pot'
    // }
	}

	// Remove money from pot
	function removeFromPot(uint256 value) public
		payable
		byOperator
		noActiveBet
	{
    // PRE: {}

		// The operator may reduce the pot (by withdrawing the requested value)
		// as long as there is no bet which is active
		require (value > 0 && value <= pot);

		pot = pot - value;
		msg.sender.transfer(value);

    // POST: { operator' == operator && state == state' && wager' == wager && timeout' == timeout &&
    //          (operator == msg.owner &&  0 < value <= pot) ==> pot' == pot - msg.value &&
    //          !(operator == msg.owner &&  0 < value <= pot) ==> pot' == pot'
    // }

	}

	// Operator opens a bet
	function createGame(bytes32 _secretNumber) public
		byOperator
		inState(State.IDLE)
	{
    // PRE: {}

		secretNumber = _secretNumber;
		state = State.GAME_AVAILABLE;

    // POST: { operator' == operator && wager' == wager && timeout' == timeout && pot == pot' &&
    //         (operator == msg.owner) ==>  state == state' &&
    //         !(operator == msg.owner) ==>  state' == State.GAME_AVAILABLE
    // }
	}

	// Player places a bet
	function placeBet(uint256 _value, Coin _guess) public
		payable
		inState (State.GAME_AVAILABLE)
		costs (_value)
	{
    // PRE: {}

		// Anyone other than the operator may place a bet as long as no other bets
		// are currently active and as long as enough money remains in the pot
		require (msg.sender != operator);
		require (_value > 0 && _value <= pot);

		state = State.BET_PLACED;
		player = msg.sender;

		wager = Wager({
			value: _value,
			guess: _guess,
			timestamp: now
		});

    // POST: { operator' == operator && timeout' == timeout && pot == pot' &&
    //          (msg.sender != operator && 0 < msg.value <= pot) ==>  wager.value == msg.value && state' == State.BET_PLACED &&
    //          !(msg.sender != operator && 0 < msg.value <= pot) ==>  wager' == wager && state' == state
    // }
	}

	// Operator resolves a bet
	function decideBet(uint publicNumber) public
		byOperator
		inState (State.BET_PLACED)
	{
    // PRE: {}

		require (secretNumber == keccak256(publicNumber));

		Coin secret = (publicNumber % 2 == 0)? Coin.HEADS: Coin.TAILS;

		if (secret == wager.guess) {
			playerWins();
		} else {
			operatorWins();
		}

		state = State.IDLE;

    // POST: { operator' == operator && timeout' == timeout && pot `elem` { pot - wager.value, pot + wager.value }
    // }

	}

	// Player resolves a bet because of operator not acting on time
	function timeoutBet() public
		inState (State.BET_PLACED)
	{
    // PRE: {}

		require (msg.sender == player);
		require (now - wager.timestamp > timeout);

		playerWins();
		state = State.IDLE;

    // POST: { operator' == operator && timeout' == timeout && pot == pot - wager.value
    // }
	}

	// Player wins and gets back twice his original wager
	function playerWins() private {
		pot = pot - wager.value;
		player.transfer(wager.value*2);
		wager.value = 0;
	}

	// Operator wins, transferring the wager to the pot
	function operatorWins() private {
		pot = pot + wager.value;
		wager.value = 0;
	}

	// Operator closes casino
	function closeCasino() public
		inState (State.IDLE)
		byOperator
	{
		selfdestruct(operator);
	}

  function () {
    // PRE: {}
    // POST: { operator' == operator && state == state' && wager' == wager && timeout' == timeout && pot' == pot }
  }

}

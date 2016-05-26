const Fn = (state={}, action) => {

  switch (action.type) {
    case 'RECEIVE_INVALID_FUNCTION':
      return {
        definition: action.definition,
        valid: false
      }
    case 'RECEIVE_VALID_FUNCTION':
      return {
        definition: action.definition,
        valid: true
      }
    default:
      return state
  }
}

export default Fn


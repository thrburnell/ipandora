const givens = (state = [], action) => {
  switch (action.type) {
    case 'ADD_GIVEN':
      return [
        ...state,
        action.id
      ]

    case 'CLEAR_PROOF':
      return []

    default:
      return state
  }
}

export default givens


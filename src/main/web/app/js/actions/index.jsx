import fetch from 'isomorphic-fetch'

export const validateFunction = (fn) => {
  return (dispatch, getState) => {

    const request = new Request('/api/predicate/function', {

      headers: new Headers({
        'Content-Type': 'application/json'
      }),
      method: 'post',
      body: JSON.stringify({
        function: fn
      })
    })

    return fetch(request)
      .then(res => res.json())
      .then(json => {
        if (json.valid) {
          console.log("Function is valid!")
          dispatch(receiveValidFunction(fn))
        } else {
          console.log("Function is invalid!")
          dispatch(receiveInvalidFunction(fn))
        }
      })
      .catch(err => console.log(err))
  }
}

export const receiveInvalidFunction = (fn) => (
  {
    type: 'RECEIVE_INVALID_FUNCTION',
    fn
  }
)

export const receiveValidFunction = (fn) => (
  {
    type: 'RECEIVE_VALID_FUNCTION',
    fn
  }
)



import { connect } from 'react-redux'
import GivensList from '../components/GivensList'

const mapStateToProps = (state) => {
  return {
    givens: state.givens
  }
}

const RGivensList = connect(
  mapStateToProps
)(GivensList)

export default RGivensList

